import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3112000 in
theorem n7l_sAA5_H_I_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · rcases h0bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h1, h11, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi3]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h0, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h1, h11, h14, hc02, hc45, hlam, hphi, ht0b, ht5b, p15_1]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h0, h13, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h1, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h4, hlam, p15_1]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h13, h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h2, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h5, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h7, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h3, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h6, hlam, p15_1]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h8, hlam, p15_0]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [h9, hlam, p15_1]
                                · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                                  linarith only [hlam, p15_0]
                              · rcases h0bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h1, h11, h13, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h13, h14, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p41_1, u1ehi4]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h0, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h1, h11, h13, h14, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h0, h13, h14, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p41_1, u1ehi4]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h1, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h4, hlam, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h13, h14, h2, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p41_1, u1ehi4]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h2, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h5, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h7, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p41_1, u1ehi4]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h3, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h6, hlam, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h8, hlam, p41_0]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [h9, hlam, p41_1]
                                · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                                  linarith only [hlam, p41_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                              · linarith only [h13, h67, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h0, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h7, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h0, h13, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h0, h13, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h1, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h4, hlam, p69_1]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h9, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h0, h13, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h2, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h5, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h7, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h13, h9, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h3, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h6, hlam, p69_1]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h8, hlam, p69_0]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [h9, hlam, p69_1]
                                · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                                  linarith only [hlam, p69_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                            · linarith only [h11, h12, h95, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                              · linarith only [h0, h11, h12, h4, h8, h95, h97, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h4, h7, h9, h97, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p99_1]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h7, h9, h97, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h9, h97, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h0, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h7, h9, h97, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h0, h12, h9, h97, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h0, h12, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h1, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h4, hlam, p99_1]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h9, h97, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h0, h12, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h2, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h5, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h7, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h12, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h3, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h6, hlam, p99_1]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h8, hlam, p99_0]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [h9, hlam, p99_1]
                                · obtain ⟨p99_0, p99_1, p99_2, p99_3⟩ := h99c
                                  linarith only [hlam, p99_0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                              · rcases h0bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi1]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h1, h125, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h11, h125, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h0, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h1, h125, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h0, h11, h125, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h1, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h4, hlam, p128_1]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h11, h125, h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h2, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h5, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h7, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p128_1, u1ehi4]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h3, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h6, hlam, p128_1]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h8, hlam, p128_0]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [h9, hlam, p128_1]
                                · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                  linarith only [hlam, p128_0]
                              · linarith only [h11, h125, h127, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                            · linarith only [h11, h125, h126, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                              · rcases h0bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi1]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi2]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi3]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h125, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi2]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h0, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi2]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi3]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h0, h125, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi2]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h1, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h4, hlam, p158_1]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi3]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h0, h125, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi2]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h2, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h5, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h7, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h125, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p158_1, u1ehi2]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h3, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h6, hlam, p158_1]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h8, hlam, p158_0]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [h9, hlam, p158_1]
                                · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                  linarith only [hlam, p158_0]
                              · linarith only [h0, h11, h157, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                              · linarith only [h0, h11, h156, h185, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                              · linarith only [h11, h185, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h188 | h188
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h190 | h190
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                              · rcases h0bigk with h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi1]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h1, h188, h191, hc01, hc45, hlam, hphi, ht0b, ht5b, p192_1]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi3]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi4]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h0, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h1, h188, h191, hc02, hc45, hlam, hphi, ht0b, ht5b, p192_1]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi3]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi4]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h1, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h4, hlam, p192_1]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi3]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi4]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h2, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h5, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h7, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p192_1, u1ehi4]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h3, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h6, hlam, p192_1]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h8, hlam, p192_0]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [h9, hlam, p192_1]
                                · obtain ⟨p192_0, p192_1, p192_2, p192_3⟩ := h192c
                                  linarith only [hlam, p192_0]
                              · rcases h0bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi1]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi2]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi3]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi4]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h0, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi2]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi3]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi4]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h1, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h4, hlam, p218_1]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi3]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi4]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h2, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h5, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h7, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p218_1, u1ehi4]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h3, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h6, hlam, p218_1]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h8, hlam, p218_0]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [h9, hlam, p218_1]
                                · obtain ⟨p218_0, p218_1, p218_2, p218_3⟩ := h218c
                                  linarith only [hlam, p218_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h190, h244, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi1]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h1, h189, h190, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h190, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h0, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h1, h189, h190, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h0, h190, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h1, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h4, hlam, p246_1]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h0, h190, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h2, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h5, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h7, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h190, h9, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p246_1, u1ehi3]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h3, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h6, hlam, p246_1]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h8, hlam, p246_0]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [h9, hlam, p246_1]
                                · obtain ⟨p246_0, p246_1, p246_2, p246_3⟩ := h246c
                                  linarith only [hlam, p246_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                            · linarith only [h188, h189, h272, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                              · linarith only [h272, h274, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi1]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h1, h188, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi3]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h189, h274, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi2]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h0, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi2]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi3]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h0, h189, h274, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi2]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h1, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h4, hlam, p276_1]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi3]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h0, h189, h274, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi2]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h2, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h5, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h7, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h189, h274, h9, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p276_1, u1ehi2]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h3, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h6, hlam, p276_1]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h8, hlam, p276_0]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [h9, hlam, p276_1]
                                · obtain ⟨p276_0, p276_1, p276_2, p276_3⟩ := h276c
                                  linarith only [hlam, p276_0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                              · rcases h0bigk with h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h188, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p305_1]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h188, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi4]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h0, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h188, h7, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi4]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h1, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h4, hlam, p305_1]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi3]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi4]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h2, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h5, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h7, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p305_1, u1ehi4]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h3, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h6, hlam, p305_1]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h8, hlam, p305_0]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [h9, hlam, p305_1]
                                · obtain ⟨p305_0, p305_1, p305_2, p305_3⟩ := h305c
                                  linarith only [hlam, p305_0]
                              · linarith only [h10, h188, h304, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                            · linarith only [h188, h302, h303, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                              · rcases h0bigk with h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h1, h10, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h2, h333, hc01, hc45, hlam, hphi, ht0b, ht5b, p335_1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi4]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h0, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h1, h10, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h0, h2, h333, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi4]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi4]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h1, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h4, hlam, p335_1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h2, h333, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi4]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi4]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h2, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h5, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h7, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h10, h302, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p335_1, u1ehi1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h3, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h6, hlam, p335_1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h8, hlam, p335_0]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [h9, hlam, p335_1]
                                · obtain ⟨p335_0, p335_1, p335_2, p335_3⟩ := h335c
                                  linarith only [hlam, p335_0]
                              · linarith only [h0, h10, h188, h334, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h362 | h362
                              · linarith only [h0, h10, h188, h333, h362, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h10, h188, h362, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h368 | h368
                            · linarith only [h2, h368, h9, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h370 | h370
                              · linarith only [h2, h370, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h0, h365, h367, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h1, h367, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h3, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h0, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h1, h367, h368, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h0, h3, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h1, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h4, hlam, p372_1]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h0, h3, h368, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h2, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h5, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h7, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h9, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h3, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h6, hlam, p372_1]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h8, hlam, p372_0]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [h2, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p372_1, u1ehi3]
                                · obtain ⟨p372_0, p372_1, p372_2, p372_3⟩ := h372c
                                  linarith only [hlam, p372_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
                            · linarith only [h367, h398, h8, h9, hc14, hlam, hphi, u1ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h400 | h400
                              · linarith only [h2, h400, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c | h402c
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h0, h365, h366, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h1, h366, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h366, h367, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h0, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h1, h366, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h0, h366, h367, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h1, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h4, hlam, p402_1]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h0, h366, h367, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h2, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h5, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h7, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h9, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h3, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h6, hlam, p402_1]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h8, hlam, p402_0]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [h2, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p402_1, u1ehi3]
                                · obtain ⟨p402_0, p402_1, p402_2, p402_3⟩ := h402c
                                  linarith only [hlam, p402_0]
                        · linarith only [h366, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h430 | h430
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                            · linarith only [h2, h431, h9, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                              · linarith only [h2, h429, h433, h9, hc13, hlam, hphi, u1ehi3]
                              · rcases h0bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h365, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi2]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h3, h431, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h0, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi2]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h0, h3, h431, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h1, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h4, hlam, p435_1]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h0, h3, h4, h431, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h2, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h5, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h7, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h9, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h3, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h6, hlam, p435_1]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h8, hlam, p435_0]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [h2, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p435_1, u1ehi3]
                                · obtain ⟨p435_0, p435_1, p435_2, p435_3⟩ := h435c
                                  linarith only [hlam, p435_0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h365, h430, h461, h8, h9, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h463 | h463
                              · linarith only [h429, h430, h463, h8, h9, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h1, h365, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi3]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h365, h430, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h0, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h1, h365, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi3]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h0, h365, h430, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h1, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h4, hlam, p465_1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi3]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h0, h365, h4, h430, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h2, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h5, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h7, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h9, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h3, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h6, hlam, p465_1]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h8, hlam, p465_0]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [h2, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p465_1, u1ehi3]
                                · obtain ⟨p465_0, p465_1, p465_2, p465_3⟩ := h465c
                                  linarith only [hlam, p465_0]
                        · linarith only [h365, h429, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h492 | h492
                    · linarith only [h492, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h495 | h495
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h496 | h496
                          · linarith only [h2, h494, h496, h7, h8, hc12, hlam, hphi, u1ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h498 | h498
                            · linarith only [h2, h492, h498, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                              · linarith only [h1, h2, h492, h495, h500, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                              · rcases h0bigk with h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c | h502c
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h0, h494, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p502_1]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h1, h495, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p502_1]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi3]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h3, h496, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi2]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h0, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi2]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi3]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h0, h3, h496, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi2]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h1, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h4, hlam, p502_1]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi3]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h8, hlam, p502_1]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h2, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h5, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h7, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h492, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h3, hlam, p502_0]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h6, hlam, p502_1]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h1, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p502_1, u1ehi2]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [h2, h500, h8, hc45, hlam, hphi, ht12, ht23, ht34, p502_1, u1ehi3]
                                · obtain ⟨p502_0, p502_1, p502_2, p502_3⟩ := h502c
                                  linarith only [hlam, p502_0]
                        · linarith only [h495, h7, h8, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h4, h494, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h530 | h530
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h531 | h531
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h1, h533, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h535 | h535
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h537 | h537
                              · rcases h0bigk with h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h0, h532, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p538_1]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi2]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h1, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi2]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi4]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h0, hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi2]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h0, h1, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi2]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi4]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h1, hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h4, hlam, p538_1]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h7, hlam, p538_1]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h3, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi4]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h2, hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h5, hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p538_1, u1ehi2]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h3, h7, hc34, hlam, hphi, ht12, ht23, p538_1, u1ehi4]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h3, hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h6, hlam, p538_1]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h530, hlam, p538_0]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [h531, hlam, p538_1]
                                · obtain ⟨p538_0, p538_1, p538_2, p538_3⟩ := h538c
                                  linarith only [hlam, p538_0]
                              · linarith only [h3, h530, h537, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                            · linarith only [h530, h531, h533, h535, h536, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                          · linarith only [h530, h535, h7, hc13, hc34, hlam, hphi]
                      · linarith only [h4, h532, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h530, h531, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h569 | h569
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                        · linarith only [h1, h571, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
                          · linarith only [h1, h530, h573, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h575 | h575
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h576 | h576
                              · rcases h0bigk with h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi1]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, h530, h569, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, h530, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h0, hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h0, h1, h530, h569, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h0, h1, h530, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h4, hlam, p577_1]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h7, hlam, p577_1]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h530, hlam, p577_1]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h2, hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h5, hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, h530, h7, hc34, hlam, hphi, ht12, ht23, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h3, hlam, p577_0]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h6, hlam, p577_1]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h1, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p577_1, u1ehi2]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [h569, hlam, p577_1]
                                · obtain ⟨p577_0, p577_1, p577_2, p577_3⟩ := h577c
                                  linarith only [hlam, p577_0]
                              · linarith only [h1, h576, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                            · linarith only [h569, h575, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h4, h570, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h607 | h607
                        · linarith only [h1, h607, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h609 | h609
                          · linarith only [h1, h530, h609, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                            · linarith only [h1, h569, h611, h7, hc14, hlam, hphi, u1ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h613 | h613
                              · linarith only [h1, h569, h613, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                              · linarith only [h1, h613, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h4, h606, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h617 | h617
                · rcases m.htr 0 3 5 (by decide) (by decide) with h618 | h618
                  · linarith only [h4, h6, h618, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                    · linarith only [h4, h6, h617, h620, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h623 | h623
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
                          · linarith only [h0, h2, h617, h618, h622, h624, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h626 | h626
                            · linarith only [h2, h620, h626, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                              · linarith only [h1, h2, h618, h620, h623, h628, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h0, h622, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p630_1]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h1, h623, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p630_1]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p630_1, u1ehi3]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p630_1, u1ehi1]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h0, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p630_1, u1ehi2]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h2, h3, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p630_1, u1ehi3]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h6, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h1, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h4, hlam, p630_1]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p630_1, u1ehi3]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h618, hlam, p630_1]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h2, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h5, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h617, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h620, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h3, hlam, p630_0]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h6, hc02, hc25, hlam, hphi, p630_1]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h2, h617, h618, h628, hc45, hlam, hphi, ht12, ht23, ht34, p630_1, u1ehi3]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [h2, h618, h628, hc45, hlam, hphi, ht12, ht23, ht34, p630_1, u1ehi3]
                                · obtain ⟨p630_0, p630_1, p630_2, p630_3⟩ := h630c
                                  linarith only [hlam, p630_0]
                        · linarith only [h4, h6, h617, h623, hc25, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h4, h6, h622, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h658 | h658
                  · linarith only [h4, h6, h658, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                    · linarith only [h5, h6, h660, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h663 | h663
                        · linarith only [h1, h617, h663, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
                          · linarith only [h1, h3, h617, h658, h665, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
                            · linarith only [h2, h660, h667, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h669 | h669
                              · linarith only [h1, h617, h660, h669, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                              · linarith only [h1, h617, h669, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h4, h6, h662, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h673 | h673
              · rcases m.htr 0 3 4 (by decide) (by decide) with h674 | h674
                · linarith only [h4, h5, h674, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h677 | h677
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
                        · linarith only [h0, h674, h676, h678, h679, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h683 | h683
                              · rcases h0bigk with h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h0, h678, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, h676, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, h4, h5, h676, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h0, hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, h676, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h5, hlam, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, h5, hc24, hlam, hphi, ht12, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h1, hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h4, hlam, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h674, hlam, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h2, hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h5, hc02, hc24, hlam, hphi, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h674, hc03, hc34, hlam, hphi, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, h674, hc34, hlam, hphi, ht12, ht23, p684_1, u1ehi4]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h3, hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h673, hlam, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h676, hlam, p684_0]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [h677, hlam, p684_1]
                                · obtain ⟨p684_0, p684_1, p684_2, p684_3⟩ := h684c
                                  linarith only [hlam, p684_0]
                              · linarith only [h3, h674, h676, h683, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                            · linarith only [h5, h677, h679, h681, h682, hc24, hlam, hphi, ht12, u1ehi4]
                          · linarith only [h4, h5, h676, h681, hc24, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h4, h5, h678, hc24, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h5, h673, h677, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h716 | h716
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h717 | h717
                        · linarith only [h1, h674, h717, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h719 | h719
                          · linarith only [h1, h676, h719, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h721 | h721
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
                              · rcases h0bigk with h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h0, h716, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h0, h5, h716, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h3, h719, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h0, hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h5, hlam, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h3, h5, h719, hc24, hlam, hphi, ht12, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h1, hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h4, hlam, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h674, hlam, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h676, hlam, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h2, hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h5, hc02, hc24, hlam, hphi, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h1, h674, hc34, hlam, hphi, ht12, ht23, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h3, h674, h719, hc34, hlam, hphi, ht12, ht23, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h3, hlam, p723_0]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h673, hlam, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h1, h673, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p723_1, u1ehi2]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [h715, hlam, p723_1]
                                · obtain ⟨p723_0, p723_1, p723_2, p723_3⟩ := h723c
                                  linarith only [hlam, p723_0]
                              · linarith only [h2, h674, h721, h722, hlam]
                            · linarith only [h674, h715, h721, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h4, h5, h716, hc12, hc24, hlam, hphi]
                    · linarith only [h5, h673, h715, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h753 | h753
                · linarith only [h4, h5, h753, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h755 | h755
                  · linarith only [h4, h673, h755, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h757 | h757
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h758 | h758
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h759 | h759
                        · linarith only [h1, h753, h759, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h761 | h761
                          · linarith only [h1, h755, h761, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h763 | h763
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h764 | h764
                              · rcases h0bigk with h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h0, h758, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p765_1, u1ehi2]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h0, h673, h757, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p765_1, u1ehi1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h0, h673, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p765_1, u1ehi1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h0, hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p765_1, u1ehi2]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h5, hlam, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h673, hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h1, hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h4, hlam, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h753, hlam, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h755, hlam, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h2, hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h5, hc02, hc24, hlam, hphi, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h1, h753, hc34, hlam, hphi, ht12, ht23, p765_1, u1ehi2]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h3, h753, h761, hc34, hlam, hphi, ht12, ht23, p765_1, u1ehi2]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h3, hlam, p765_0]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h1, h4, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p765_1, u1ehi2]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h1, h755, hc35, hlam, hphi, ht12, ht23, p765_1, u1ehi2]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [h757, hlam, p765_1]
                                · obtain ⟨p765_0, p765_1, p765_2, p765_3⟩ := h765c
                                  linarith only [hlam, p765_0]
                              · linarith only [h2, h753, h763, h764, hlam]
                            · linarith only [h5, h757, h759, h763, hc24, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h4, h5, h758, hc24, hlam, hphi, ht12, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
                        · linarith only [h1, h753, h795, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h797 | h797
                          · linarith only [h1, h755, h797, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                            · linarith only [h1, h4, h5, h757, h799, hc14, hlam, hphi, u1ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h801 | h801
                              · linarith only [h1, h4, h5, h757, h801, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                              · linarith only [h1, h753, h801, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h4, h753, h794, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h805 | h805
            · rcases m.htr 0 2 5 (by decide) (by decide) with h806 | h806
              · rcases m.htr 0 3 4 (by decide) (by decide) with h807 | h807
                · rcases m.htr 0 3 5 (by decide) (by decide) with h808 | h808
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
                      · linarith only [h2, h4, h805, h810, hc12, hlam, hphi, u1ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h813 | h813
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h814 | h814
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h815 | h815
                              · rcases h0bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h805, h809, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h4, h805, h809, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h809, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h0, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h4, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h809, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h4, hc23, hlam, hphi, ht12, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h1, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h805, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p816_1]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h4, h809, hc23, hlam, hphi, ht12, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h4, hc23, hlam, hphi, ht12, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h2, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h805, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h807, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, h805, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p816_1, u1ehi4]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h3, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h806, hlam, p816_1]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h808, hlam, p816_0]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [h809, hlam, p816_1]
                                · obtain ⟨p816_0, p816_1, p816_2, p816_3⟩ := h816c
                                  linarith only [hlam, p816_0]
                              · rcases h0bigk with h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h806, hc01, hc25, hlam, hphi, ht0b, ht5b, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h1, h812, h814, h815, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h2, h814, h815, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p842_1, u1ehi4]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h0, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h4, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h2, h814, h815, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h3, h4, hc23, hlam, hphi, ht12, p842_1, u1ehi4]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h1, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h2, h805, h814, h815, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h2, h4, h814, h815, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h3, h4, hc23, hlam, hphi, ht12, p842_1, u1ehi4]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h2, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h805, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h807, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h3, h805, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p842_1, u1ehi4]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h3, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h806, hlam, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h808, hlam, p842_0]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [h809, hlam, p842_1]
                                · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                  linarith only [hlam, p842_0]
                            · linarith only [h4, h805, h809, h814, hc23, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h4, h808, h810, h813, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h4, h807, h810, h812, hc23, hlam, hphi, ht12, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
                      · linarith only [h0, h4, h871, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h875 | h875
                            · linarith only [h2, h809, h875, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h877 | h877
                              · linarith only [h2, h809, h873, h877, hc13, hlam, hphi, u1ehi3]
                              · rcases h0bigk with h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, h806, h809, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p879_1, u1ehi2]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, h809, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h0, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h4, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, h4, h809, hc23, hlam, hphi, ht12, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h1, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h4, hc02, hc23, hlam, hphi, p879_1]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, h4, hc23, hlam, hphi, ht12, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, h4, h809, hc23, hlam, hphi, ht12, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h805, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h807, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h809, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h3, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h806, hlam, p879_1]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h808, hlam, p879_0]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [h2, h806, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p879_1, u1ehi3]
                                · obtain ⟨p879_0, p879_1, p879_2, p879_3⟩ := h879c
                                  linarith only [hlam, p879_0]
                          · linarith only [h4, h808, h871, h874, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h4, h807, h871, h873, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h4, h806, h808, hlam]
                · linarith only [h4, h805, h807, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h909 | h909
                · rcases m.htr 0 3 5 (by decide) (by decide) with h910 | h910
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h911 | h911
                    · linarith only [h805, h806, h911, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h913 | h913
                      · linarith only [h0, h4, h913, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h916 | h916
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h917 | h917
                            · linarith only [h2, h911, h917, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h919 | h919
                              · linarith only [h2, h911, h919, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, h805, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, h805, h806, h910, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, h805, h806, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h0, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h4, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h806, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h1, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h4, hc02, hc23, hlam, hphi, p921_1]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, h4, hc23, hlam, hphi, ht12, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h3, h4, h917, hc23, hlam, hphi, ht12, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h805, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h909, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h911, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h3, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, h805, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h910, hlam, p921_0]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [h2, h911, hc45, hlam, hphi, ht12, ht23, ht34, p921_1, u1ehi3]
                                · obtain ⟨p921_0, p921_1, p921_2, p921_3⟩ := h921c
                                  linarith only [hlam, p921_0]
                          · linarith only [h4, h910, h916, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h4, h909, h913, h915, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h949 | h949
                    · linarith only [h805, h806, h949, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h951 | h951
                      · linarith only [h2, h4, h805, h951, hc12, hlam, hphi, u1ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h953 | h953
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h954 | h954
                          · linarith only [h1, h910, h954, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                            · linarith only [h2, h949, h956, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h958 | h958
                              · linarith only [h2, h949, h958, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                              · rcases h0bigk with h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, h805, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, h4, h805, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, h4, h805, h910, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h0, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h4, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h806, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h1, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h910, hc02, hc35, hlam, hphi, ht23, p960_1]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, h910, h958, hc45, hlam, hphi, ht12, ht23, ht34, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h910, hlam, p960_1]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h805, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h909, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h949, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h3, hlam, p960_0]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, h805, h806, hc25, hlam, hphi, ht12, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h910, h958, hc03, hc45, hlam, hphi, ht34, p960_1]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [h2, h910, h958, hc45, hlam, hphi, ht12, ht23, ht34, p960_1, u1ehi3]
                                · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                  linarith only [hlam, p960_0]
                        · linarith only [h4, h909, h951, h953, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h4, h805, h909, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h988 | h988
              · rcases m.htr 0 3 4 (by decide) (by decide) with h989 | h989
                · rcases m.htr 0 3 5 (by decide) (by decide) with h990 | h990
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h991 | h991
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h992 | h992
                      · linarith only [h3, h4, h988, h992, hc12, hlam, hphi, u1ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h994 | h994
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h995 | h995
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h996 | h996
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h997 | h997
                              · rcases h0bigk with h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, h805, h988, h989, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, h805, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h0, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h4, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h805, hlam, p998_1]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h1, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h988, hc03, hc25, hlam, hphi, ht0b, ht5b, p998_1]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h2, h4, h996, hc23, hlam, hphi, ht12, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, h4, hc23, hlam, hphi, ht12, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h2, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, h988, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h989, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, h4, h989, hc23, hlam, hphi, ht12, p998_1, u1ehi4]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h3, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h988, hlam, p998_1]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h990, hlam, p998_0]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [h991, hlam, p998_1]
                                · obtain ⟨p998_0, p998_1, p998_2, p998_3⟩ := h998c
                                  linarith only [hlam, p998_0]
                              · rcases h0bigk with h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi4]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h1, h994, h996, h997, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1024_1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h2, h996, h997, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1024_1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi4]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h0, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h4, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h805, hlam, p1024_1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi4]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h1, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h2, h4, h996, h997, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1024_1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, h4, hc23, hlam, hphi, ht12, p1024_1, u1ehi4]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h2, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, h988, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi4]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h989, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, h4, h989, hc23, hlam, hphi, ht12, p1024_1, u1ehi4]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h3, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h988, hlam, p1024_1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h990, hlam, p1024_0]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [h991, hlam, p1024_1]
                                · obtain ⟨p1024_0, p1024_1, p1024_2, p1024_3⟩ := h1024c
                                  linarith only [hlam, p1024_0]
                            · linarith only [h4, h989, h991, h996, hc23, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h4, h990, h992, h995, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h4, h989, h992, h994, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h805, h988, h991, hlam]
                  · linarith only [h4, h988, h990, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1055 | h1055
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1057 | h1057
                      · linarith only [h0, h1057, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1059 | h1059
                        · linarith only [h1059, h3, h4, h988, h989, hc13, hlam, hphi, u1ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1061 | h1061
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1062 | h1062
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
                              · rcases h0bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, h4, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, h4, h988, h989, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h0, hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h4, hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h805, hlam, p1064_1]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h1, hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h989, hc02, hc34, hlam, hphi, ht23, p1064_1]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h989, hlam, p1064_1]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, h989, hc34, hlam, hphi, ht12, ht23, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h2, hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, h988, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h989, hc03, hc34, hlam, hphi, p1064_1]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, h989, hc34, hlam, hphi, ht12, ht23, p1064_1, u1ehi4]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h3, hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h988, hlam, p1064_1]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h1055, hlam, p1064_0]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [h1056, hlam, p1064_1]
                                · obtain ⟨p1064_0, p1064_1, p1064_2, p1064_3⟩ := h1064c
                                  linarith only [hlam, p1064_0]
                              · linarith only [h1063, h3, h4, h988, h989, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                            · linarith only [h1056, h1057, h1059, h1062, h805, hc24, hlam, hphi, ht12, u1ehi1]
                          · linarith only [h1055, h1057, h1061, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h1056, h4, h988, h989, hlam]
                  · linarith only [h1055, h4, h988, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1095 | h1095
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1096 | h1096
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1097 | h1097
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1098 | h1098
                      · linarith only [h0, h1098, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1100 | h1100
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1101 | h1101
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1102 | h1102
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1103 | h1103
                              · rcases h0bigk with h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1, u1ehi1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1, h1100, h1103, hc01, hc45, hlam, hphi, ht0b, ht5b, p1104_1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1102, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1, u1ehi4]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1, u1ehi4]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h4, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h805, hlam, p1104_1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h988, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1, u1ehi1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1102, h2, h4, hc23, hlam, hphi, ht12, p1104_1, u1ehi4]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, h4, h988, hc23, hlam, hphi, ht12, p1104_1, u1ehi1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h2, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1, u1ehi1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1095, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, h1095, h4, h988, hc23, hlam, hphi, ht12, p1104_1, u1ehi1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h3, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1104_1, u1ehi1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1096, hlam, p1104_0]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [h1097, hlam, p1104_1]
                                · obtain ⟨p1104_0, p1104_1, p1104_2, p1104_3⟩ := h1104c
                                  linarith only [hlam, p1104_0]
                              · rcases h0bigk with h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi2]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1102, h1103, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1130_1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi4]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h4, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h805, hlam, p1130_1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h988, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1102, h1103, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1130_1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, h4, h988, hc23, hlam, hphi, ht12, p1130_1, u1ehi1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h2, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1095, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, h1095, h4, h988, hc23, hlam, hphi, ht12, p1130_1, u1ehi1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h3, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1096, hlam, p1130_0]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [h1097, hlam, p1130_1]
                                · obtain ⟨p1130_0, p1130_1, p1130_2, p1130_3⟩ := h1130c
                                  linarith only [hlam, p1130_0]
                            · linarith only [h1095, h1097, h1102, h4, hc23, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h1096, h1098, h1101, h4, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h1095, h1098, h1100, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
                      · linarith only [h0, h1159, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1161 | h1161
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1162 | h1162
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1163 | h1163
                            · linarith only [h1097, h1163, h2, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1165 | h1165
                              · linarith only [h0, h1097, h1161, h1165, h805, hc13, hlam, hphi, u1ehi1]
                              · rcases h0bigk with h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi2]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, h805, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1163, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi3]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h4, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h805, hlam, p1167_1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h988, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, h4, h805, hc23, hlam, hphi, ht12, p1167_1, u1ehi1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1163, h3, h4, hc23, hlam, hphi, ht12, p1167_1, u1ehi3]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h2, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1095, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1097, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h3, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1167_1, u1ehi1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1096, hlam, p1167_0]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [h1097, hc04, hc45, hlam, hphi, p1167_1]
                                · obtain ⟨p1167_0, p1167_1, p1167_2, p1167_3⟩ := h1167c
                                  linarith only [hlam, p1167_0]
                          · linarith only [h1096, h1159, h1162, h4, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h1095, h1159, h1161, h4, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1195 | h1195
                    · linarith only [h1095, h1096, h1195, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
                      · linarith only [h0, h1197, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1200 | h1200
                          · linarith only [h1, h1096, h1200, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1202 | h1202
                            · linarith only [h0, h1195, h1202, h805, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1204 | h1204
                              · linarith only [h0, h1, h1195, h1199, h1204, h805, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · rcases h0bigk with h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c | h1206c
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h1, h1199, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1206_1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, h805, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1206_1, u1ehi4]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h4, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h805, hlam, p1206_1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h988, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h1, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, h4, h805, hc23, hlam, hphi, ht12, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h1096, hlam, p1206_1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h2, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h1095, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h1195, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h3, hlam, p1206_0]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h1096, h1204, hc03, hc45, hlam, hphi, ht34, p1206_1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [h0, h1096, h1204, h805, hc45, hlam, hphi, ht12, ht23, ht34, p1206_1, u1ehi1]
                                · obtain ⟨p1206_0, p1206_1, p1206_2, p1206_3⟩ := h1206c
                                  linarith only [hlam, p1206_0]
                        · linarith only [h1095, h1197, h1199, h4, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1233 | h1233
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1234 | h1234
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1235 | h1235
                      · linarith only [h0, h1235, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1237 | h1237
                        · linarith only [h1, h1095, h1233, h1237, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1239 | h1239
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1240 | h1240
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1241 | h1241
                              · rcases h0bigk with h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h1233, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h1095, h1233, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h988, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h4, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h805, hlam, p1242_1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h988, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h1, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h1095, hlam, p1242_1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h1095, h988, hc34, hlam, hphi, ht12, ht23, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h2, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h1095, hc34, hlam, hphi, ht12, ht23, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h1095, hc03, hc34, hlam, hphi, p1242_1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h1095, h988, hc34, hlam, hphi, ht12, ht23, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h3, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h0, h1233, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u1ehi1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h1233, hlam, p1242_0]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [h1234, hlam, p1242_1]
                                · obtain ⟨p1242_0, p1242_1, p1242_2, p1242_3⟩ := h1242c
                                  linarith only [hlam, p1242_0]
                              · linarith only [h1, h1095, h1235, h1241, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                            · linarith only [h1095, h1233, h1234, h1235, h1237, h1240, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h1095, h1233, h1235, h1239, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h1095, h1233, h1234, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1272 | h1272
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1273 | h1273
                      · linarith only [h0, h1273, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1275 | h1275
                        · linarith only [h0, h1095, h1275, h4, hc13, hlam, hphi, u1ehi1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1277 | h1277
                          · linarith only [h1, h1233, h1277, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1279 | h1279
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1280 | h1280
                              · rcases h0bigk with h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, h1233, h1272, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, h1233, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h4, hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h805, hlam, p1281_1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h988, hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h1, hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h1095, hlam, p1281_1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h1233, hlam, p1281_1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h2, hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, h805, hc24, hlam, hphi, ht12, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h1095, hc03, hc34, hlam, hphi, p1281_1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h1095, h3, hc34, hlam, hphi, ht12, ht23, p1281_1, u1ehi4]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h3, hlam, p1281_0]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h0, h1233, h1280, h4, hc34, hlam, hphi, ht12, ht23, p1281_1, u1ehi1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [h1272, hlam, p1281_1]
                                · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                  linarith only [hlam, p1281_0]
                              · linarith only [h0, h1095, h1280, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                            · linarith only [h1272, h1279, h805, hc24, hlam, hphi, ht12, u1ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
                      · linarith only [h0, h1309, h4, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1311 | h1311
                        · linarith only [h0, h1095, h1311, h4, hc13, hlam, hphi, u1ehi1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1313 | h1313
                          · linarith only [h1, h1095, h1233, h1313, h3, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1315 | h1315
                            · linarith only [h0, h1095, h1272, h1315, h4, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1317 | h1317
                              · linarith only [h0, h1095, h1272, h1317, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h1095, h1317, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1323 | h1323
    · linarith only [h0, h1323, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1325 | h1325
      · linarith only [h0, h1325, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1327 | h1327
        · linarith only [h0, h1327, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1329 | h1329
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1330 | h1330
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1331 | h1331
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1332 | h1332
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1333 | h1333
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1334 | h1334
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1335 | h1335
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1337 | h1337
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1338 | h1338
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1339 | h1339
                              · rcases h0bigk with h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h0, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1323, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1325, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1327, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h0, h1332, h1339, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h0, h1327, h1334, hc12, hlam, hphi, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h0, h1327, hc12, hlam, hphi, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1329, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1327, h1334, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h0, h1327, h1329, hc12, hlam, hphi, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1330, hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1332, hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h0, h1327, h1329, h1332, hc12, hlam, hphi, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1340_1, u1ehi0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1331, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1333, hlam, p1340_0]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [h1334, hlam, p1340_1]
                                · obtain ⟨p1340_0, p1340_1, p1340_2, p1340_3⟩ := h1340c
                                  linarith only [hlam, p1340_0]
                              · rcases h0bigk with h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h0, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1323, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1325, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1327, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h0, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h0, h1323, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h0, h1327, h1334, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h0, h1327, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1329, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1323, h1327, h1334, h1335, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1323, h1327, h1335, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1330, hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1332, hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1325, h1327, h1335, h1336, hc12, hlam, hphi, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1366_1, u1ehi0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1331, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1333, hlam, p1366_0]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [h1334, hlam, p1366_1]
                                · obtain ⟨p1366_0, p1366_1, p1366_2, p1366_3⟩ := h1366c
                                  linarith only [hlam, p1366_0]
                            · linarith only [h1325, h1338, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                          · linarith only [h1323, h1337, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h1323, h1336, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1335, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1396 | h1396
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1397 | h1397
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1398 | h1398
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
                            · linarith only [h1325, h1334, h1396, h1397, h1399, hc12, hlam, hphi, u1ehi0]
                            · linarith only [h1325, h1399, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                          · linarith only [h1323, h1398, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h1323, h1397, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1329, h1396, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1405 | h1405
                    · linarith only [h1332, h1333, h1405, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1407 | h1407
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1408 | h1408
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1409 | h1409
                          · linarith only [h1323, h1333, h1409, hc13, hlam, hphi, u1ehi0]
                          · linarith only [h1323, h1409, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h1323, h1332, h1333, h1408, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h1329, h1333, h1407, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1414 | h1414
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1415 | h1415
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1416 | h1416
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1417 | h1417
                        · linarith only [h1323, h1332, h1416, h1417, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1417, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1416, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h1332, h1414, h1415, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1422 | h1422
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1423 | h1423
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1424 | h1424
                        · linarith only [h1323, h1332, h1424, hc13, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1424, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h1329, h1414, h1423, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1429 | h1429
                        · linarith only [h1323, h1332, h1428, h1429, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1429, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1428, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1433 | h1433
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1434 | h1434
                  · linarith only [h1329, h1331, h1434, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1436 | h1436
                    · linarith only [h1330, h1331, h1436, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1438 | h1438
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1439 | h1439
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1440 | h1440
                          · linarith only [h1323, h1434, h1438, h1440, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h1323, h1440, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h1323, h1439, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1329, h1438, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1445 | h1445
                  · linarith only [h1329, h1331, h1445, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1447 | h1447
                    · linarith only [h1330, h1331, h1447, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1449 | h1449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1450 | h1450
                        · linarith only [h1323, h1433, h1450, hc13, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1450, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1329, h1449, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1454 | h1454
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1455 | h1455
                · linarith only [h1329, h1330, h1455, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1457 | h1457
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1458 | h1458
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1459 | h1459
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1460 | h1460
                        · linarith only [h1323, h1455, h1460, hc13, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1460, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1329, h1459, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h1329, h1330, h1457, h1458, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1465 | h1465
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1466 | h1466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1467 | h1467
                        · linarith only [h1323, h1455, h1466, h1467, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1467, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1329, h1466, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h1330, h1454, h1465, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1472 | h1472
                · linarith only [h1329, h1330, h1472, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1474 | h1474
                  · linarith only [h1329, h1454, h1474, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1476 | h1476
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1477 | h1477
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1478 | h1478
                        · linarith only [h1323, h1472, h1477, h1478, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1478, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h1329, h1454, h1477, hc12, hc25, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1482 | h1482
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1483 | h1483
                        · linarith only [h1323, h1472, h1482, h1483, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1323, h1483, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h1329, h1330, h1476, h1482, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1487 | h1487
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1488 | h1488
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1489 | h1489
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1490 | h1490
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1491 | h1491
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1492 | h1492
                      · linarith only [h0, h1329, h1492, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1492, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1495 | h1495
                      · linarith only [h0, h1329, h1495, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1495, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1329, h1488, h1490, hlam]
                · linarith only [h1329, h1487, h1489, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1500 | h1500
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1501 | h1501
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1502 | h1502
                    · linarith only [h1487, h1488, h1502, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1504 | h1504
                      · linarith only [h0, h1329, h1504, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1504, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
                    · linarith only [h1329, h1487, h1501, h1507, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1509 | h1509
                      · linarith only [h1325, h1329, h1487, h1509, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1509, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h1329, h1487, h1500, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1513 | h1513
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1514 | h1514
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1515 | h1515
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1516 | h1516
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1517 | h1517
                      · linarith only [h0, h1329, h1517, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1517, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h1487, h1513, h1516, hlam]
                  · linarith only [h1487, h1513, h1514, h1515, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1522 | h1522
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1523 | h1523
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1524 | h1524
                      · linarith only [h0, h1329, h1524, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1524, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h1329, h1513, h1514, h1523, hlam]
                  · linarith only [h1329, h1513, h1522, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1529 | h1529
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1530 | h1530
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1531 | h1531
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1532 | h1532
                      · linarith only [h0, h1329, h1532, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1532, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1535 | h1535
                      · linarith only [h0, h1329, h1535, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1535, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1538 | h1538
                    · linarith only [h1529, h1530, h1538, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
                      · linarith only [h0, h1329, h1540, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1540, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1543 | h1543
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1544 | h1544
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1545 | h1545
                      · linarith only [h0, h1329, h1545, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1545, hc23, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h1529, h1543, h1544, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1549 | h1549
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1550 | h1550
                      · linarith only [h0, h1329, h1550, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1550, hc23, hlam, hphi, ht12, u1ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1553 | h1553
                      · linarith only [h0, h1329, h1553, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h1553, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA5_H_R_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
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
                                      · linarith only [h0, h15, h17, h21, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                      · rcases h1bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
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
                                          linarith only [h0, h11, h15, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h2, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h10, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h12, hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [hlam, p23_0]
                                        · obtain ⟨p23_0, p23_1, p23_2, p23_3⟩ := h23c
                                          linarith only [h11, h15, h17, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23_1]
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
                                          linarith only [h12, h50, h53, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, h50, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h10, h52, hc01, hc45, hlam, hphi, ht0b, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h13, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, h50, h53, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, h12, h50, h53, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h0, h13, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h1, hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h9, hlam, p54_1]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [hlam, p54_0]
                                        · obtain ⟨p54_0, p54_1, p54_2, p54_3⟩ := h54c
                                          linarith only [h12, h50, h53, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p54_1]
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
                                      · linarith only [h0, h10, h52, h53, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
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
                                  · linarith only [h0, h12, h125, h14, h4, h6, h8, h84, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                                    · linarith only [h0, h10, h12, h127, h14, h84, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                  · linarith only [h0, h13, h160, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                                    · linarith only [h10, h157, h162, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                                      · linarith only [h10, h13, h157, h159, h164, h9, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                      · rcases h1bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
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
                                          linarith only [h0, h10, h159, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h0, h13, h159, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h1, hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h9, hlam, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [h1, h10, h159, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
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
                                          linarith only [h0, h10, h13, h159, h164, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                        · obtain ⟨p166_0, p166_1, p166_2, p166_3⟩ := h166c
                                          linarith only [hlam, p166_0]
                                · linarith only [h12, h13, h159, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                                · linarith only [h12, h199, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                                      · rcases h1bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [hlam, p204_0]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h201, h203, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                        · obtain ⟨p204_0, p204_1, p204_2, p204_3⟩ := h204c
                                          linarith only [h12, h201, h203, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
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
                                          linarith only [h0, h12, h201, h203, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
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
                                          linarith only [h0, h12, h197, h203, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p204_1]
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
                                      · linarith only [h0, h12, h201, h203, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h12, h197, h198, h199, h201, h202, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h12, h197, h201, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h12, h197, h198, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                                · linarith only [h12, h239, h9, hlam]
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
                                          linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, h10, h243, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                        · obtain ⟨p245_0, p245_1, p245_2, p245_3⟩ := h245c
                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p245_1]
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
                                          linarith only [h11, h12, h241, hc23, hc34, hlam, hphi, p245_1]
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
                                      · linarith only [h12, h238, h244, hlam]
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
                                          linarith only [h238, hc01, hc45, hlam, hphi, ht0b, ht5b, p281_1]
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
                                          linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p281_1]
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
                                          linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h0, h11, h12, h239, h243, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h3, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h11, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p281_1]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [h238, hlam, p281_0]
                                        · obtain ⟨p281_0, p281_1, p281_2, p281_3⟩ := h281c
                                          linarith only [hlam, p281_0]
                                      · linarith only [h12, h238, h280, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                                · linarith only [h12, h312, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h314 | h314
                                  · linarith only [h0, h197, h314, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                          linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
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
                                          linarith only [h0, h197, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p319_1]
                                        · obtain ⟨p319_0, p319_1, p319_2, p319_3⟩ := h319c
                                          linarith only [h0, h238, h318, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p319_1]
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
                                          linarith only [h197, h318, hc14, hc45, hlam, hphi, p357_1]
                                        · obtain ⟨p357_0, p357_1, p357_2, p357_3⟩ := h357c
                                          linarith only [hlam, p357_0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h396 | h396
                            · linarith only [h11, h396, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
                              · linarith only [h10, h11, h398, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                                · linarith only [h0, h11, h400, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h395, h396, h4, h400, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                            · linarith only [h10, h11, h395, h403, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                              · linarith only [h10, h11, h405, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                                · linarith only [h0, h11, h395, h407, h5, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                                  · linarith only [h11, h403, h409, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                                    · linarith only [h0, h10, h11, h4, h409, h411, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                                      · linarith only [h0, h10, h11, h4, h407, h411, h413, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                          linarith only [h0, h11, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p415_1]
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
                                          linarith only [h0, h4, h403, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [h0, h4, h405, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p415_1]
                                        · obtain ⟨p415_0, p415_1, p415_2, p415_3⟩ := h415c
                                          linarith only [hlam, p415_0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                          · linarith only [h10, h450, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                                · linarith only [h10, h450, h454, h9, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h456 | h456
                                  · linarith only [h0, h10, h4, h454, h456, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h10, h4, h452, h454, h456, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h10, h452, h453, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h460 | h460
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h461 | h461
                                · linarith only [h10, h450, h461, h9, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h463 | h463
                                  · linarith only [h0, h10, h4, h461, h463, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h466 | h466
                                      · rcases h1bigk with h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h449, h463, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
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
                                          linarith only [h10, h9, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h10, hlam, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h461, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p467_1]
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
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h461, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [hlam, p467_0]
                                        · obtain ⟨p467_0, p467_1, p467_2, p467_3⟩ := h467c
                                          linarith only [h0, h10, h4, h449, h461, h463, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p467_1]
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
                                      · linarith only [h10, h449, h461, h465, h466, hlam]
                                    · linarith only [h10, h449, h463, h465, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h10, h449, h460, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                          · linarith only [h10, h504, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                            · linarith only [h449, h506, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h509 | h509
                                · linarith only [h0, h449, h5, h504, h509, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                          linarith only [h0, h10, h4, h509, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h0, h10, h4, h449, h509, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h3, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h9, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h0, h4, h449, h509, h513, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p515_1]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [h508, hlam, p515_0]
                                        · obtain ⟨p515_0, p515_1, p515_2, p515_3⟩ := h515c
                                          linarith only [hlam, p515_0]
                                      · linarith only [h10, h508, h509, h514, hlam]
                                    · linarith only [h10, h508, h513, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h547 | h547
                                · linarith only [h0, h10, h4, h508, h547, h6, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h549 | h549
                                  · linarith only [h0, h10, h4, h508, h549, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h551 | h551
                                    · linarith only [h10, h508, h547, h551, h9, hc23, hc34, hlam, hphi]
                                    · linarith only [h0, h10, h4, h551, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                  · linarith only [h0, h4, h555, h560, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                · linarith only [h555, h559, h6, h9, hc03, hc25, hlam, hphi, ht0b, ht5b]
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
                                          linarith only [h554, h566, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h554, h566, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
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
                                          linarith only [h0, h554, h566, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h0, h4, h554, h558, h566, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p572_1]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h1, hlam, p572_0]
                                        · obtain ⟨p572_0, p572_1, p572_2, p572_3⟩ := h572c
                                          linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p572_1]
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
                                  · linarith only [h0, h4, h554, h566, h567, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h4, h554, h566, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
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
                                          linarith only [h0, h4, h554, h555, h6, h614, h616, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p620_1]
                                        · obtain ⟨p620_0, p620_1, p620_2, p620_3⟩ := h620c
                                          linarith only [hlam, p620_0]
                                  · linarith only [h0, h4, h554, h614, h615, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h4, h554, h6, h614, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h652 | h652
                              · linarith only [h554, h555, h652, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h655 | h655
                                  · linarith only [h0, h4, h554, h611, h654, h655, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h4, h554, h654, h655, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h4, h554, h6, h654, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h554, h610, h9, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h665 | h665
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                                      · rcases h1bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h660, h665, h667, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h661, h667, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h554, h660, h665, h667, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          rcases p668_3 (m.d 0 1) (by simp) with h673 | h673
                                          · rcases p668_3 (m.d 1 2) (by simp) with h674 | h674
                                            · linarith only [h0, h674, hlam]
                                            · linarith only [h660, h674, hlam]
                                          · linarith only [h673, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h0, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h9, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h554, hlam, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h554, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h1, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h0, h4, h554, h660, h665, h667, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h0, h4, h660, h665, h667, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h2, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h660, h665, h667, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h661, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h0, h4, h660, h661, h665, h667, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h3, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h660, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h662, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [h663, hlam, p668_0]
                                        · obtain ⟨p668_0, p668_1, p668_2, p668_3⟩ := h668c
                                          linarith only [hlam, p668_0]
                                      · linarith only [h0, h4, h660, h666, h667, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h3, h554, h660, h663, h666, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h4, h554, h660, h664, h665, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h4, h6, h660, h664, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h554, h660, h663, hlam]
                            · linarith only [h660, h662, h9, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h704 | h704
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h705 | h705
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h706 | h706
                                · linarith only [h0, h4, h661, h704, h706, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h4, h6, h660, h706, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h660, h661, h705, h9, hlam]
                            · linarith only [h660, h704, h9, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h711 | h711
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h712 | h712
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h713 | h713
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h716 | h716
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h717 | h717
                                      · rcases h1bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          rcases p718_3 (m.d 0 1) (by simp) with h720 | h720
                                          · rcases p718_3 (m.d 1 2) (by simp) with h721 | h721
                                            · linarith only [h721, hlam, p718_0]
                                            · rcases p718_3 (m.d 1 3) (by simp) with h723 | h723
                                              · linarith only [h1, h723, hlam]
                                              · linarith only [h723, h9, hlam]
                                          · linarith only [h720, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h711, h717, hc01, hc45, hlam, hphi, ht0b, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h711, h717, hc01, hc45, hlam, hphi, ht0b, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          rcases p718_3 (m.d 0 1) (by simp) with h729 | h729
                                          · rcases p718_3 (m.d 1 2) (by simp) with h730 | h730
                                            · linarith only [h0, h730, hlam]
                                            · rcases p718_3 (m.d 1 3) (by simp) with h732 | h732
                                              · linarith only [h1, h732, hlam]
                                              · linarith only [h712, h732, hlam]
                                          · linarith only [h729, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h0, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h9, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h554, hlam, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h660, hlam, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h1, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h9, hc12, hc23, hlam, hphi, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h0, h4, h711, h717, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h2, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h711, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h0, h4, h554, h660, h714, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h3, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p718_1]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h712, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [h713, hlam, p718_0]
                                        · obtain ⟨p718_0, p718_1, p718_2, p718_3⟩ := h718c
                                          linarith only [hlam, p718_0]
                                      · rcases h1bigk with h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c | h756c
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          rcases p756_3 (m.d 0 1) (by simp) with h758 | h758
                                          · rcases p756_3 (m.d 1 2) (by simp) with h759 | h759
                                            · linarith only [h759, hlam, p756_0]
                                            · rcases p756_3 (m.d 1 3) (by simp) with h761 | h761
                                              · linarith only [h1, h761, hlam]
                                              · linarith only [h761, h9, hlam]
                                          · linarith only [h758, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h711, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h713, h717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h713, h717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h0, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h9, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h554, hlam, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h660, hlam, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h1, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h0, h4, h713, h717, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h2, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h711, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h0, h4, h554, h660, h714, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h3, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p756_1]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h712, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [h713, hlam, p756_0]
                                        · obtain ⟨p756_0, p756_1, p756_2, p756_3⟩ := h756c
                                          linarith only [hlam, p756_0]
                                    · linarith only [h554, h713, h716, hlam]
                                  · linarith only [h712, h715, h9, hlam]
                                · linarith only [h711, h714, h9, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h791 | h791
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h792 | h792
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h793 | h793
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h794 | h794
                                      · linarith only [h1, h554, h711, h713, h794, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          rcases p796_3 (m.d 0 1) (by simp) with h798 | h798
                                          · rcases p796_3 (m.d 1 2) (by simp) with h799 | h799
                                            · linarith only [h799, hlam, p796_0]
                                            · rcases p796_3 (m.d 1 3) (by simp) with h801 | h801
                                              · linarith only [h1, h801, hlam]
                                              · linarith only [h801, h9, hlam]
                                          · linarith only [h798, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h711, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          rcases p796_3 (m.d 0 1) (by simp) with h806 | h806
                                          · rcases p796_3 (m.d 1 2) (by simp) with h807 | h807
                                            · linarith only [h0, h807, hlam]
                                            · rcases p796_3 (m.d 1 3) (by simp) with h809 | h809
                                              · linarith only [h1, h809, hlam]
                                              · linarith only [h711, h809, hlam]
                                          · linarith only [h806, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          rcases p796_3 (m.d 0 1) (by simp) with h813 | h813
                                          · rcases p796_3 (m.d 1 2) (by simp) with h814 | h814
                                            · linarith only [h0, h814, hlam]
                                            · rcases p796_3 (m.d 1 3) (by simp) with h816 | h816
                                              · linarith only [h1, h816, hlam]
                                              · linarith only [h712, h816, hlam]
                                          · linarith only [h813, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h0, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h9, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h554, hlam, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h660, hlam, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h1, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h0, h4, h554, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h2, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h713, h793, hc12, hc24, hlam, hphi, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h711, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h713, hlam, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h3, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h712, hlam, p796_0]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [h713, h793, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p796_1]
                                        · obtain ⟨p796_0, p796_1, p796_2, p796_3⟩ := h796c
                                          linarith only [hlam, p796_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h840 | h840
                                      · linarith only [h554, h793, h840, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c | h842c
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          rcases p842_3 (m.d 0 1) (by simp) with h844 | h844
                                          · rcases p842_3 (m.d 1 2) (by simp) with h845 | h845
                                            · linarith only [h845, hlam, p842_0]
                                            · rcases p842_3 (m.d 1 3) (by simp) with h847 | h847
                                              · linarith only [h1, h847, hlam]
                                              · linarith only [h847, h9, hlam]
                                          · linarith only [h844, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h711, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          rcases p842_3 (m.d 0 1) (by simp) with h852 | h852
                                          · rcases p842_3 (m.d 1 2) (by simp) with h853 | h853
                                            · linarith only [h0, h853, hlam]
                                            · rcases p842_3 (m.d 1 3) (by simp) with h855 | h855
                                              · linarith only [h1, h855, hlam]
                                              · linarith only [h711, h855, hlam]
                                          · linarith only [h852, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          rcases p842_3 (m.d 0 1) (by simp) with h859 | h859
                                          · rcases p842_3 (m.d 1 2) (by simp) with h860 | h860
                                            · linarith only [h0, h860, hlam]
                                            · rcases p842_3 (m.d 1 3) (by simp) with h862 | h862
                                              · linarith only [h1, h862, hlam]
                                              · linarith only [h712, h862, hlam]
                                          · linarith only [h859, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h0, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h9, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h554, hlam, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h660, hlam, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h1, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h0, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h0, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h2, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h711, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h713, hlam, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h3, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h712, hlam, p842_0]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [h0, h4, h6, h660, h793, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p842_1]
                                        · obtain ⟨p842_0, p842_1, p842_2, p842_3⟩ := h842c
                                          linarith only [hlam, p842_0]
                                  · linarith only [h712, h792, h9, hlam]
                                · linarith only [h711, h791, h9, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h888 | h888
                              · linarith only [h711, h712, h888, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                                  · linarith only [h0, h4, h711, h712, h891, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                                    · linarith only [h0, h4, h7, h888, h890, h891, h893, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                                      · linarith only [h554, h711, h893, h895, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          rcases p897_3 (m.d 0 1) (by simp) with h899 | h899
                                          · rcases p897_3 (m.d 1 2) (by simp) with h900 | h900
                                            · linarith only [h900, hlam, p897_0]
                                            · rcases p897_3 (m.d 1 3) (by simp) with h902 | h902
                                              · linarith only [h1, h902, hlam]
                                              · linarith only [h9, h902, hlam]
                                          · linarith only [h899, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h711, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          rcases p897_3 (m.d 0 1) (by simp) with h907 | h907
                                          · rcases p897_3 (m.d 1 2) (by simp) with h908 | h908
                                            · linarith only [h0, h908, hlam]
                                            · rcases p897_3 (m.d 1 3) (by simp) with h910 | h910
                                              · linarith only [h1, h910, hlam]
                                              · linarith only [h711, h910, hlam]
                                          · linarith only [h907, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h711, h712, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h0, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h9, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h554, hlam, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h660, hlam, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h1, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h4, h554, h6, h8, h891, h895, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h712, hlam, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h2, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h711, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h888, hlam, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h3, hlam, p897_0]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h0, h4, h6, h660, h8, h891, h895, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [h0, h4, h554, h6, h660, h8, h891, h895, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p897_1]
                                        · obtain ⟨p897_0, p897_1, p897_2, p897_3⟩ := h897c
                                          linarith only [hlam, p897_0]
                                · linarith only [h1, h711, h890, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h936 | h936
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h938 | h938
                                · linarith only [h0, h4, h711, h936, h938, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h941 | h941
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h942 | h942
                                      · rcases h1bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          rcases p943_3 (m.d 0 1) (by simp) with h945 | h945
                                          · rcases p943_3 (m.d 1 2) (by simp) with h946 | h946
                                            · linarith only [h946, hlam, p943_0]
                                            · rcases p943_3 (m.d 1 3) (by simp) with h948 | h948
                                              · linarith only [h1, h948, hlam]
                                              · linarith only [h9, h948, hlam]
                                          · linarith only [h945, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h936, h942, hc01, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h711, h936, h942, hc01, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          rcases p943_3 (m.d 0 1) (by simp) with h954 | h954
                                          · rcases p943_3 (m.d 1 2) (by simp) with h955 | h955
                                            · linarith only [h0, h955, hlam]
                                            · rcases p943_3 (m.d 1 3) (by simp) with h957 | h957
                                              · linarith only [h1, h957, hlam]
                                              · linarith only [h936, h957, hlam]
                                          · linarith only [h954, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h0, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h9, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h554, hlam, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h660, hlam, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h1, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h711, hlam, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h2, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h0, h4, h6, h711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h0, h4, h6, h711, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h0, h4, h6, h660, h711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h3, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p943_1]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h936, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [h937, hlam, p943_0]
                                        · obtain ⟨p943_0, p943_1, p943_2, p943_3⟩ := h943c
                                          linarith only [hlam, p943_0]
                                      · linarith only [h0, h4, h6, h8, h9, h938, h942, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                    · linarith only [h554, h9, h936, h937, h938, h941, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h9, h936, h940, hlam]
                              · linarith only [h711, h936, h937, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h985 | h985
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h986 | h986
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h987 | h987
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h988 | h988
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h989 | h989
                                      · rcases h1bigk with h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c | h990c
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          rcases p990_3 (m.d 0 1) (by simp) with h992 | h992
                                          · rcases p990_3 (m.d 1 2) (by simp) with h993 | h993
                                            · linarith only [h993, hlam, p990_0]
                                            · rcases p990_3 (m.d 1 3) (by simp) with h995 | h995
                                              · linarith only [h1, h995, hlam]
                                              · linarith only [h9, h995, hlam]
                                          · linarith only [h992, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          rcases p990_3 (m.d 0 1) (by simp) with h999 | h999
                                          · rcases p990_3 (m.d 1 2) (by simp) with h1000 | h1000
                                            · linarith only [h0, h1000, hlam]
                                            · rcases p990_3 (m.d 1 3) (by simp) with h1002 | h1002
                                              · linarith only [h1002, hlam, p990_0]
                                              · rcases p990_3 (m.d 1 4) (by simp) with h1004 | h1004
                                                · linarith only [h1004, h2, hlam]
                                                · linarith only [h1004, h711, hlam]
                                          · linarith only [h999, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h985, hc01, hc45, hlam, hphi, ht0b, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          rcases p990_3 (m.d 0 1) (by simp) with h1009 | h1009
                                          · rcases p990_3 (m.d 1 2) (by simp) with h1010 | h1010
                                            · linarith only [h0, h1010, hlam]
                                            · rcases p990_3 (m.d 1 3) (by simp) with h1012 | h1012
                                              · linarith only [h1, h1012, hlam]
                                              · rcases p990_3 (m.d 1 4) (by simp) with h1014 | h1014
                                                · linarith only [h1014, h2, hlam]
                                                · linarith only [h1014, h985, hlam]
                                          · linarith only [h1009, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h0, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h9, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h554, hlam, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h660, hlam, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h1, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h0, h4, h936, h986, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h711, hlam, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h936, hlam, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h2, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h0, h4, h711, h986, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h0, h4, h711, h9, h936, h986, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h3, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h0, h4, h9, h936, h986, h989, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p990_1]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [h985, hlam, p990_0]
                                        · obtain ⟨p990_0, p990_1, p990_2, p990_3⟩ := h990c
                                          linarith only [hlam, p990_0]
                                      · linarith only [h711, h985, h989, hlam]
                                    · linarith only [h554, h711, h985, h988, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h4, h7, h711, h985, h986, h987, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1041 | h1041
                                  · linarith only [h1041, h9, h936, h986, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1043 | h1043
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1044 | h1044
                                      · rcases h1bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          rcases p1045_3 (m.d 0 1) (by simp) with h1047 | h1047
                                          · rcases p1045_3 (m.d 1 2) (by simp) with h1048 | h1048
                                            · linarith only [h1048, hlam, p1045_0]
                                            · rcases p1045_3 (m.d 1 3) (by simp) with h1050 | h1050
                                              · linarith only [h1, h1050, hlam]
                                              · linarith only [h1050, h9, hlam]
                                          · linarith only [h1047, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          rcases p1045_3 (m.d 0 1) (by simp) with h1054 | h1054
                                          · rcases p1045_3 (m.d 1 2) (by simp) with h1055 | h1055
                                            · linarith only [h0, h1055, hlam]
                                            · rcases p1045_3 (m.d 1 3) (by simp) with h1057 | h1057
                                              · linarith only [h1057, hlam, p1045_0]
                                              · rcases p1045_3 (m.d 1 4) (by simp) with h1059 | h1059
                                                · linarith only [h1059, h2, hlam]
                                                · linarith only [h1059, h711, hlam]
                                          · linarith only [h1054, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h985, hc01, hc45, hlam, hphi, ht0b, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          rcases p1045_3 (m.d 0 1) (by simp) with h1064 | h1064
                                          · rcases p1045_3 (m.d 1 2) (by simp) with h1065 | h1065
                                            · linarith only [h0, h1065, hlam]
                                            · rcases p1045_3 (m.d 1 3) (by simp) with h1067 | h1067
                                              · linarith only [h1, h1067, hlam]
                                              · rcases p1045_3 (m.d 1 4) (by simp) with h1069 | h1069
                                                · linarith only [h1069, h2, hlam]
                                                · linarith only [h1069, h985, hlam]
                                          · linarith only [h1064, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h0, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h9, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h554, hlam, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h660, hlam, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h1, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h711, hlam, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h936, hlam, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h2, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h0, h4, h554, h6, h986, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h0, h4, h554, h6, h986, hc01, hc15, hlam, hphi, ht0b, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h3, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h0, h1043, h4, h6, h660, h9, h986, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1045_1]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [h985, hlam, p1045_0]
                                        · obtain ⟨p1045_0, p1045_1, p1045_2, p1045_3⟩ := h1045c
                                          linarith only [hlam, p1045_0]
                                      · linarith only [h1044, h554, h985, h986, hlam]
                                    · linarith only [h1043, h554, h985, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1096 | h1096
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1098 | h1098
                                      · linarith only [h0, h1095, h1098, h4, h985, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                      · linarith only [h0, h1095, h1097, h1098, h4, h711, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1101 | h1101
                                      · linarith only [h0, h1097, h1101, h4, h554, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          rcases p1103_3 (m.d 0 1) (by simp) with h1105 | h1105
                                          · rcases p1103_3 (m.d 1 2) (by simp) with h1106 | h1106
                                            · linarith only [h1106, hlam, p1103_0]
                                            · rcases p1103_3 (m.d 1 3) (by simp) with h1108 | h1108
                                              · linarith only [h1, h1108, hlam]
                                              · linarith only [h1108, h9, hlam]
                                          · linarith only [h1105, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          rcases p1103_3 (m.d 0 1) (by simp) with h1112 | h1112
                                          · rcases p1103_3 (m.d 1 2) (by simp) with h1113 | h1113
                                            · linarith only [h0, h1113, hlam]
                                            · rcases p1103_3 (m.d 1 3) (by simp) with h1115 | h1115
                                              · linarith only [h1115, hlam, p1103_0]
                                              · rcases p1103_3 (m.d 1 4) (by simp) with h1117 | h1117
                                                · linarith only [h1117, h2, hlam]
                                                · linarith only [h1117, h711, hlam]
                                          · linarith only [h1112, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          rcases p1103_3 (m.d 0 1) (by simp) with h1121 | h1121
                                          · rcases p1103_3 (m.d 1 2) (by simp) with h1122 | h1122
                                            · linarith only [h0, h1122, hlam]
                                            · rcases p1103_3 (m.d 1 3) (by simp) with h1124 | h1124
                                              · linarith only [h1, h1124, hlam]
                                              · rcases p1103_3 (m.d 1 4) (by simp) with h1126 | h1126
                                                · linarith only [h1126, hlam, p1103_0]
                                                · rcases p1103_3 (m.d 1 5) (by simp) with h1128 | h1128
                                                  · linarith only [h1128, h3, hlam]
                                                  · linarith only [h1128, h985, hlam]
                                          · linarith only [h1121, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          rcases p1103_3 (m.d 0 1) (by simp) with h1132 | h1132
                                          · rcases p1103_3 (m.d 1 2) (by simp) with h1133 | h1133
                                            · linarith only [h0, h1133, hlam]
                                            · rcases p1103_3 (m.d 1 3) (by simp) with h1135 | h1135
                                              · linarith only [h1, h1135, hlam]
                                              · rcases p1103_3 (m.d 1 4) (by simp) with h1137 | h1137
                                                · linarith only [h1137, h2, hlam]
                                                · rcases p1103_3 (m.d 1 5) (by simp) with h1139 | h1139
                                                  · linarith only [h1139, hlam, p1103_0]
                                                  · rcases h5bigk with h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      rcases p1141_3 (m.d 0 5) (by simp) with h1143 | h1143
                                                      · rcases p1141_3 (m.d 1 5) (by simp) with h1144 | h1144
                                                        · linarith only [h1144, h3, hlam]
                                                        · rcases p1141_3 (m.d 2 5) (by simp) with h1146 | h1146
                                                          · linarith only [h1146, h5, hlam]
                                                          · linarith only [h1146, h660, hlam]
                                                      · linarith only [h1143, h3, hlam]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      rcases p1141_3 (m.d 0 5) (by simp) with h1150 | h1150
                                                      · rcases p1141_3 (m.d 1 5) (by simp) with h1151 | h1151
                                                        · linarith only [h1151, h3, hlam]
                                                        · rcases p1141_3 (m.d 2 5) (by simp) with h1153 | h1153
                                                          · linarith only [h1153, h5, hlam]
                                                          · rcases p1141_3 (m.d 3 5) (by simp) with h1155 | h1155
                                                            · linarith only [h1155, h7, hlam]
                                                            · rcases p1141_3 (m.d 4 5) (by simp) with h1157 | h1157
                                                              · linarith only [h1157, h8, hlam]
                                                              · linarith only [h1097, h1157, hlam]
                                                      · linarith only [h1150, h5, hlam]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      rcases p1141_3 (m.d 0 5) (by simp) with h1161 | h1161
                                                      · rcases p1141_3 (m.d 1 5) (by simp) with h1162 | h1162
                                                        · linarith only [h1162, h3, hlam]
                                                        · rcases p1141_3 (m.d 2 5) (by simp) with h1164 | h1164
                                                          · linarith only [h1164, h5, hlam]
                                                          · linarith only [h1096, h1164, hlam]
                                                      · linarith only [h1161, h7, hlam]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h0, h1095, h1097, h4, h6, h711, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h3, hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h660, hlam, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h936, hlam, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h985, hlam, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h5, hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      rcases p1141_3 (m.d 0 5) (by simp) with h1175 | h1175
                                                      · rcases p1141_3 (m.d 1 5) (by simp) with h1176 | h1176
                                                        · linarith only [h1176, h660, hlam]
                                                        · rcases p1141_3 (m.d 2 5) (by simp) with h1178 | h1178
                                                          · rcases p1141_3 (m.d 3 5) (by simp) with h1179 | h1179
                                                            · linarith only [h1096, h1179, hlam]
                                                            · linarith only [h1179, h936, hlam]
                                                          · linarith only [h1178, h660, hlam]
                                                      · linarith only [h1175, h3, hlam]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h9, h936, hc12, hc25, hlam, hphi, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h1097, hlam, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h7, hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h0, h1096, h4, h711, h9, h985, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h1096, hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h1101, hlam, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h8, hlam, p1141_0]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      rcases p1141_3 (m.d 0 5) (by simp) with h1193 | h1193
                                                      · rcases p1141_3 (m.d 1 5) (by simp) with h1194 | h1194
                                                        · linarith only [h1194, h985, hlam]
                                                        · rcases p1141_3 (m.d 2 5) (by simp) with h1196 | h1196
                                                          · linarith only [h1097, h1196, hlam]
                                                          · linarith only [h1196, h660, hlam]
                                                      · linarith only [h1193, h3, hlam]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h0, h4, h6, h660, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [h0, h4, h6, h8, h9, h936, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1141_1]
                                                    · obtain ⟨p1141_0, p1141_1, p1141_2, p1141_3⟩ := h1141c
                                                      linarith only [hlam, p1141_0]
                                          · linarith only [h1132, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h0, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h9, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h554, hlam, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h660, hlam, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h1, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h1095, h711, hc12, hc24, hlam, hphi, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h711, hlam, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h936, hlam, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h2, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h0, h5, h660, h985, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h985, hlam, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h3, hlam, p1103_0]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h0, h5, h660, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h0, h4, h7, h9, h936, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [h0, h4, h7, h936, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1103_1]
                                        · obtain ⟨p1103_0, p1103_1, p1103_2, p1103_3⟩ := h1103c
                                          linarith only [hlam, p1103_0]
                                  · linarith only [h0, h1095, h1096, h4, h7, h711, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1225 | h1225
                                  · linarith only [h1095, h1225, h9, h936, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1227 | h1227
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1228 | h1228
                                      · rcases h1bigk with h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c | h1229c
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          rcases p1229_3 (m.d 0 1) (by simp) with h1231 | h1231
                                          · rcases p1229_3 (m.d 1 2) (by simp) with h1232 | h1232
                                            · linarith only [h1232, hlam, p1229_0]
                                            · rcases p1229_3 (m.d 1 3) (by simp) with h1234 | h1234
                                              · linarith only [h1, h1234, hlam]
                                              · linarith only [h1234, h9, hlam]
                                          · linarith only [h1231, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          rcases p1229_3 (m.d 0 1) (by simp) with h1238 | h1238
                                          · rcases p1229_3 (m.d 1 2) (by simp) with h1239 | h1239
                                            · linarith only [h0, h1239, hlam]
                                            · rcases p1229_3 (m.d 1 3) (by simp) with h1241 | h1241
                                              · linarith only [h1241, hlam, p1229_0]
                                              · rcases p1229_3 (m.d 1 4) (by simp) with h1243 | h1243
                                                · linarith only [h1243, h2, hlam]
                                                · linarith only [h1243, h711, hlam]
                                          · linarith only [h1238, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          rcases p1229_3 (m.d 0 1) (by simp) with h1247 | h1247
                                          · rcases p1229_3 (m.d 1 2) (by simp) with h1248 | h1248
                                            · linarith only [h0, h1248, hlam]
                                            · rcases p1229_3 (m.d 1 3) (by simp) with h1250 | h1250
                                              · linarith only [h1, h1250, hlam]
                                              · rcases p1229_3 (m.d 1 4) (by simp) with h1252 | h1252
                                                · linarith only [h1252, hlam, p1229_0]
                                                · rcases p1229_3 (m.d 1 5) (by simp) with h1254 | h1254
                                                  · linarith only [h1254, h3, hlam]
                                                  · linarith only [h1254, h985, hlam]
                                          · linarith only [h1247, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          rcases p1229_3 (m.d 0 1) (by simp) with h1258 | h1258
                                          · rcases p1229_3 (m.d 1 2) (by simp) with h1259 | h1259
                                            · linarith only [h0, h1259, hlam]
                                            · rcases p1229_3 (m.d 1 3) (by simp) with h1261 | h1261
                                              · linarith only [h1, h1261, hlam]
                                              · rcases p1229_3 (m.d 1 4) (by simp) with h1263 | h1263
                                                · linarith only [h1263, h2, hlam]
                                                · rcases p1229_3 (m.d 1 5) (by simp) with h1265 | h1265
                                                  · linarith only [h1265, hlam, p1229_0]
                                                  · rcases h5bigk with h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      rcases p1267_3 (m.d 0 5) (by simp) with h1269 | h1269
                                                      · rcases p1267_3 (m.d 1 5) (by simp) with h1270 | h1270
                                                        · linarith only [h1270, h3, hlam]
                                                        · rcases p1267_3 (m.d 2 5) (by simp) with h1272 | h1272
                                                          · linarith only [h1272, h5, hlam]
                                                          · linarith only [h1272, h660, hlam]
                                                      · linarith only [h1269, h3, hlam]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      rcases p1267_3 (m.d 0 5) (by simp) with h1276 | h1276
                                                      · rcases p1267_3 (m.d 1 5) (by simp) with h1277 | h1277
                                                        · linarith only [h1277, h3, hlam]
                                                        · rcases p1267_3 (m.d 2 5) (by simp) with h1279 | h1279
                                                          · linarith only [h1279, h5, hlam]
                                                          · rcases p1267_3 (m.d 3 5) (by simp) with h1281 | h1281
                                                            · linarith only [h1281, h7, hlam]
                                                            · linarith only [h1225, h1281, hlam]
                                                      · linarith only [h1276, h5, hlam]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h0, h1225, h4, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      rcases p1267_3 (m.d 0 5) (by simp) with h1286 | h1286
                                                      · rcases p1267_3 (m.d 1 5) (by simp) with h1287 | h1287
                                                        · linarith only [h1287, h3, hlam]
                                                        · rcases p1267_3 (m.d 2 5) (by simp) with h1289 | h1289
                                                          · linarith only [h1289, h5, hlam]
                                                          · linarith only [h1227, h1289, hlam]
                                                      · linarith only [h1286, h8, hlam]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h3, hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h660, hlam, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h936, hlam, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h985, hlam, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h5, hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      rcases p1267_3 (m.d 0 5) (by simp) with h1299 | h1299
                                                      · rcases p1267_3 (m.d 1 5) (by simp) with h1300 | h1300
                                                        · linarith only [h1300, h660, hlam]
                                                        · rcases p1267_3 (m.d 2 5) (by simp) with h1302 | h1302
                                                          · rcases p1267_3 (m.d 3 5) (by simp) with h1303 | h1303
                                                            · rcases p1267_3 (m.d 4 5) (by simp) with h1304 | h1304
                                                              · linarith only [h1227, h1304, hlam]
                                                              · linarith only [h1304, h985, hlam]
                                                            · linarith only [h1303, h936, hlam]
                                                          · linarith only [h1302, h660, hlam]
                                                      · linarith only [h1299, h3, hlam]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h1225, hlam, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h711, h9, h985, hc12, hc25, hlam, hphi, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h7, hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      rcases p1267_3 (m.d 0 5) (by simp) with h1314 | h1314
                                                      · rcases p1267_3 (m.d 1 5) (by simp) with h1315 | h1315
                                                        · linarith only [h1315, h936, hlam]
                                                        · rcases p1267_3 (m.d 2 5) (by simp) with h1317 | h1317
                                                          · linarith only [h1225, h1317, hlam]
                                                          · linarith only [h1317, h660, hlam]
                                                      · linarith only [h1314, h3, hlam]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h0, h1228, h4, h6, h660, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h0, h1228, h4, h6, h711, h9, h985, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h8, hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h0, h1095, h1227, h4, h6, h711, h9, h985, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1267_1]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h1227, hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [h1228, hlam, p1267_0]
                                                    · obtain ⟨p1267_0, p1267_1, p1267_2, p1267_3⟩ := h1267c
                                                      linarith only [hlam, p1267_0]
                                          · linarith only [h1258, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h0, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h9, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h554, hlam, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h660, hlam, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h1, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h711, hlam, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h936, hlam, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h2, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h0, h1095, h4, h554, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h0, h1095, h4, h554, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h985, hlam, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h3, hlam, p1229_0]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h0, h5, h660, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h0, h1228, h4, h6, h9, h936, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [h0, h1228, h4, h6, h936, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1229_1]
                                        · obtain ⟨p1229_0, p1229_1, p1229_2, p1229_3⟩ := h1229c
                                          linarith only [hlam, p1229_0]
                                      · linarith only [h1095, h1227, h1228, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1351 | h1351
                                      · linarith only [h0, h1095, h1227, h1351, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · linarith only [h1095, h1351, h9, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                · linarith only [h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc25, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, ht01, u0ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

set_option maxHeartbeats 5488000 in
theorem n7l_sAA5_M_LI_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h16, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                  · linarith only [h0, h10, h19, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h13, h19, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h13, h14, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h13, h23, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                  · linarith only [h0, h13, h26, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                    · linarith only [h0, h10, h23, h28, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                                      · rcases h0bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h23, h30, h4, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h10, h23, h30, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h2, h25, hc45, hlam, hphi, ht01, ht0b, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h10, h23, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h0, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h10, h23, h30, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u0elo1]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h0, h10, h23, h30, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h0, h10, h23, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h1, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h4, hlam, p31_1]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h10, h23, h30, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u0elo2]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h0, h10, h23, h4, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p31_1, u1elo0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h2, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h5, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h7, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h10, h23, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u0elo3]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h3, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h6, hlam, p31_1]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h8, hlam, p31_0]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [h9, hlam, p31_1]
                                        · obtain ⟨p31_0, p31_1, p31_2, p31_3⟩ := h31c
                                          linarith only [hlam, p31_0]
                                      · linarith only [h0, h10, h13, h30, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                                  · linarith only [h10, h13, h58, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                    · linarith only [h10, h23, h60, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                                      · linarith only [h0, h25, h4, h62, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · linarith only [h10, h13, h62, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
                          · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h67 | h67
                        · linarith only [h0, h10, h4, h67, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h69 | h69
                          · linarith only [h0, h10, h4, h69, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h72 | h72
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                                      · linarith only [h1, h71, h76, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                      · linarith only [h2, h73, h76, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h10, h72, h75, hlam]
                                  · linarith only [h0, h10, h4, h7, h72, h74, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h83 | h83
                                      · linarith only [h71, h73, h83, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                      · rcases h0bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h10, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h5, h67, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h5, h67, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h6, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h0, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h5, h67, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u0elo1]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h0, h5, h67, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h0, h6, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h1, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h4, hlam, p85_1]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h5, h67, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u0elo2]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h0, h4, h6, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1, u1elo0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h2, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h5, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h7, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h6, h69, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u0elo3]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h3, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h6, hlam, p85_1]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h8, hlam, p85_0]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [h9, hlam, p85_1]
                                        · obtain ⟨p85_0, p85_1, p85_2, p85_3⟩ := h85c
                                          linarith only [hlam, p85_0]
                                    · linarith only [h67, h81, h82, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h1, h71, h81, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h71, h72, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                              · linarith only [h0, h114, h4, h7, h71, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                                  · linarith only [h0, h117, h4, h71, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h117, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                                  · linarith only [h0, h10, h120, h4, h71, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h120, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h128 | h128
                                · linarith only [h128, h2, h9, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                                  · linarith only [h0, h123, h130, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h130, h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h126, h127, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h126, h7, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h123, h125, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h123, h124, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                        · linarith only [h0, h123, h137, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h137, h5, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                            · linarith only [h141, h146, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                                  · linarith only [h0, h1, h143, h148, h150, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                                    · linarith only [h0, h144, h150, h152, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h148, h152, h7, hc23, hc34, hlam, hphi]
                                · linarith only [h146, h148, h149, hc35, hlam, hphi, u5elo4]
                              · linarith only [h141, h148, h7, hc13, hc34, hlam, hphi]
                          · linarith only [h143, h145, hc23, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h0, h143, h144, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                        · linarith only [h0, h143, h159, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                          · linarith only [h0, h143, h161, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                            · linarith only [h141, h163, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h165 | h165
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h166 | h166
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                                  · linarith only [h167, h4, h7, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h169 | h169
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                                      · rcases h0bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h143, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h141, h161, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h141, h161, h6, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h161, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h0, hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h141, h161, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p171_1, u0elo1]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h0, h141, h161, h6, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h0, h161, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h1, hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h4, hlam, p171_1]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h7, hlam, p171_1]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h161, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p171_1, u0elo2]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h2, hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h5, hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h0, h141, h170, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h0, h161, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h3, hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h6, hlam, p171_1]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h141, hlam, p171_0]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [h142, hlam, p171_1]
                                        · obtain ⟨p171_0, p171_1, p171_2, p171_3⟩ := h171c
                                          linarith only [hlam, p171_0]
                                      · linarith only [h141, h161, h170, h6, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                    · linarith only [h1, h165, h169, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h142, h163, h165, h166, hc35, hlam, hphi, u5elo0]
                              · linarith only [h141, h165, h7, hc13, hc34, hlam, hphi]
                    · linarith only [h141, h142, h7, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h202 | h202
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                            · linarith only [h1, h206, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                              · linarith only [h1, h141, h208, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                                  · linarith only [h0, h203, h211, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                                    · linarith only [h0, h141, h204, h211, h213, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h215 | h215
                                      · rcases h0bigk with h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c | h216c
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h0, h204, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p216_1, u1elo0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          rcases p216_3 (m.d 0 1) (by simp) with h219 | h219
                                          · rcases p216_3 (m.d 0 2) (by simp) with h220 | h220
                                            · linarith only [h0, h220, hlam]
                                            · linarith only [h220, h4, hlam]
                                          · linarith only [h1, h219, hlam]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h2, h210, hc45, hlam, hphi, ht01, ht0b, ht5b, p216_1, u1elo0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          rcases p216_3 (m.d 0 1) (by simp) with h225 | h225
                                          · rcases p216_3 (m.d 0 2) (by simp) with h226 | h226
                                            · linarith only [h0, h226, hlam]
                                            · linarith only [h226, h6, hlam]
                                          · linarith only [h225, h3, hlam]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h0, hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          rcases p216_3 (m.d 0 1) (by simp) with h232 | h232
                                          · rcases p216_3 (m.d 0 2) (by simp) with h233 | h233
                                            · rcases p216_3 (m.d 0 3) (by simp) with h234 | h234
                                              · linarith only [h234, h4, hlam]
                                              · rcases p216_3 (m.d 0 4) (by simp) with h236 | h236
                                                · linarith only [h236, h5, hlam]
                                                · linarith only [h236, h7, hlam]
                                            · linarith only [h233, h4, hlam]
                                          · linarith only [h1, h232, hlam]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h2, h210, hc45, hlam, hphi, ht0b, ht5b, p216_1, u0elo1]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          rcases p216_3 (m.d 0 1) (by simp) with h242 | h242
                                          · rcases p216_3 (m.d 0 2) (by simp) with h243 | h243
                                            · rcases p216_3 (m.d 0 3) (by simp) with h244 | h244
                                              · linarith only [h244, h4, hlam]
                                              · rcases p216_3 (m.d 0 4) (by simp) with h246 | h246
                                                · linarith only [h246, h5, hlam]
                                                · linarith only [h202, h246, hlam]
                                            · linarith only [h243, h6, hlam]
                                          · linarith only [h242, h3, hlam]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h1, hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h4, hlam, p216_1]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h7, hlam, p216_1]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h141, hlam, p216_1]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h2, hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h5, hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          rcases p216_3 (m.d 0 1) (by simp) with h258 | h258
                                          · rcases p216_3 (m.d 0 2) (by simp) with h259 | h259
                                            · rcases p216_3 (m.d 0 3) (by simp) with h260 | h260
                                              · linarith only [h260, h7, hlam]
                                              · rcases p216_3 (m.d 0 4) (by simp) with h262 | h262
                                                · rcases p216_3 (m.d 0 5) (by simp) with h263 | h263
                                                  · linarith only [h202, h263, hlam]
                                                  · linarith only [h141, h263, hlam]
                                                · linarith only [h262, h7, hlam]
                                            · linarith only [h259, h4, hlam]
                                          · linarith only [h1, h258, hlam]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          rcases p216_3 (m.d 0 1) (by simp) with h270 | h270
                                          · rcases p216_3 (m.d 0 2) (by simp) with h271 | h271
                                            · rcases p216_3 (m.d 0 3) (by simp) with h272 | h272
                                              · linarith only [h272, h7, hlam]
                                              · rcases p216_3 (m.d 0 4) (by simp) with h274 | h274
                                                · rcases p216_3 (m.d 0 5) (by simp) with h275 | h275
                                                  · linarith only [h202, h275, hlam]
                                                  · rcases h1bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h204, h211, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      rcases p277_3 (m.d 0 1) (by simp) with h280 | h280
                                                      · rcases p277_3 (m.d 1 2) (by simp) with h281 | h281
                                                        · linarith only [h0, h281, hlam]
                                                        · linarith only [h203, h281, hlam]
                                                      · linarith only [h280, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h210, hc45, hlam, hphi, ht01, ht0b, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      rcases p277_3 (m.d 0 1) (by simp) with h286 | h286
                                                      · rcases p277_3 (m.d 1 2) (by simp) with h287 | h287
                                                        · linarith only [h0, h287, hlam]
                                                        · linarith only [h205, h287, hlam]
                                                      · linarith only [h286, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h0, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h0, h203, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h0, h210, hc45, hlam, hphi, ht01, ht0b, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h0, h203, h208, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h1, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h203, hlam, p277_1]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h206, hlam, p277_1]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h208, hlam, p277_1]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h2, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h204, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h2, h203, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h0, h203, h204, h208, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p277_1, u1elo0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h3, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h205, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h203, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p216_1, p277_1, u0elo3]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [h210, hlam, p277_0]
                                                    · obtain ⟨p277_0, p277_1, p277_2, p277_3⟩ := h277c
                                                      linarith only [hlam, p277_0]
                                                · linarith only [h202, h274, hlam]
                                            · linarith only [h271, h6, hlam]
                                          · linarith only [h270, h3, hlam]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h3, hlam, p216_0]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h6, hlam, p216_1]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h1, h141, h203, hc23, hlam, hphi, ht34, ht45, p216_1, u5elo3]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [h202, hlam, p216_1]
                                        · obtain ⟨p216_0, p216_1, p216_2, p216_3⟩ := h216c
                                          linarith only [hlam, p216_0]
                                      · linarith only [h1, h203, h215, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                                  · linarith only [h1, h202, h203, h210, h320, h7, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                                    · linarith only [h0, h141, h202, h203, h206, h210, h322, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                                      · rcases h0bigk with h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p325_1, u1elo0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          rcases p325_3 (m.d 0 1) (by simp) with h328 | h328
                                          · rcases p325_3 (m.d 0 2) (by simp) with h329 | h329
                                            · linarith only [h0, h329, hlam]
                                            · linarith only [h329, h4, hlam]
                                          · linarith only [h1, h328, hlam]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h202, h204, h210, h320, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p325_1, u1elo0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h202, h204, h210, h320, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p325_1, u1elo0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h0, hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          rcases p325_3 (m.d 0 1) (by simp) with h337 | h337
                                          · rcases p325_3 (m.d 0 2) (by simp) with h338 | h338
                                            · rcases p325_3 (m.d 0 3) (by simp) with h339 | h339
                                              · linarith only [h339, h4, hlam]
                                              · rcases p325_3 (m.d 0 4) (by simp) with h341 | h341
                                                · linarith only [h341, h5, hlam]
                                                · linarith only [h341, h7, hlam]
                                            · linarith only [h338, h4, hlam]
                                          · linarith only [h1, h337, hlam]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h202, h204, h210, h320, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p325_1, u0elo1]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h0, h202, h204, h210, h320, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p325_1, u1elo0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h1, hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h4, hlam, p325_1]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h7, hlam, p325_1]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h141, hlam, p325_1]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h2, hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h5, hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          rcases p325_3 (m.d 0 1) (by simp) with h355 | h355
                                          · rcases p325_3 (m.d 0 2) (by simp) with h356 | h356
                                            · rcases p325_3 (m.d 0 3) (by simp) with h357 | h357
                                              · linarith only [h357, h7, hlam]
                                              · rcases p325_3 (m.d 0 4) (by simp) with h359 | h359
                                                · rcases p325_3 (m.d 0 5) (by simp) with h360 | h360
                                                  · linarith only [h202, h360, hlam]
                                                  · linarith only [h141, h360, hlam]
                                                · linarith only [h359, h7, hlam]
                                            · linarith only [h356, h4, hlam]
                                          · linarith only [h1, h355, hlam]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h202, h204, h210, h320, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p325_1, u0elo3]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h3, hlam, p325_0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h6, hlam, p325_1]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h1, h203, hc23, hlam, hphi, ht34, ht45, p325_1, u5elo0]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [h202, hlam, p325_1]
                                        · obtain ⟨p325_0, p325_1, p325_2, p325_3⟩ := h325c
                                          linarith only [hlam, p325_0]
                                      · linarith only [h1, h203, h324, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h203, h205, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
                        · linarith only [h0, h203, h204, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h141, h203, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h379 | h379
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h380 | h380
                            · linarith only [h1, h380, h7, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h382 | h382
                              · linarith only [h1, h141, h202, h382, h7, hc05, hlam, hphi, u5elo4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h384 | h384
                                · linarith only [h2, h202, h384, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                                  · linarith only [h1, h377, h386, h7, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                                    · linarith only [h1, h141, h377, h388, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                                      · rcases h0bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h0, h378, h386, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p391_1, u1elo0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          rcases p391_3 (m.d 0 1) (by simp) with h394 | h394
                                          · rcases p391_3 (m.d 0 2) (by simp) with h395 | h395
                                            · linarith only [h0, h395, hlam]
                                            · linarith only [h395, h4, hlam]
                                          · linarith only [h1, h394, hlam]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          rcases p391_3 (m.d 0 1) (by simp) with h399 | h399
                                          · rcases p391_3 (m.d 0 2) (by simp) with h400 | h400
                                            · linarith only [h0, h400, hlam]
                                            · linarith only [h400, h5, hlam]
                                          · linarith only [h2, h399, hlam]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          rcases p391_3 (m.d 0 1) (by simp) with h404 | h404
                                          · rcases p391_3 (m.d 0 2) (by simp) with h405 | h405
                                            · linarith only [h0, h405, hlam]
                                            · linarith only [h405, h6, hlam]
                                          · linarith only [h3, h404, hlam]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h0, hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          rcases p391_3 (m.d 0 1) (by simp) with h411 | h411
                                          · rcases p391_3 (m.d 0 2) (by simp) with h412 | h412
                                            · rcases p391_3 (m.d 0 3) (by simp) with h413 | h413
                                              · linarith only [h4, h413, hlam]
                                              · rcases p391_3 (m.d 0 4) (by simp) with h415 | h415
                                                · linarith only [h415, h5, hlam]
                                                · linarith only [h415, h7, hlam]
                                            · linarith only [h4, h412, hlam]
                                          · linarith only [h1, h411, hlam]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          rcases p391_3 (m.d 0 1) (by simp) with h420 | h420
                                          · rcases p391_3 (m.d 0 2) (by simp) with h421 | h421
                                            · rcases p391_3 (m.d 0 3) (by simp) with h422 | h422
                                              · linarith only [h4, h422, hlam]
                                              · rcases p391_3 (m.d 0 4) (by simp) with h424 | h424
                                                · linarith only [h424, h5, hlam]
                                                · rcases p391_3 (m.d 0 5) (by simp) with h426 | h426
                                                  · linarith only [h426, h6, hlam]
                                                  · linarith only [h202, h426, hlam]
                                            · linarith only [h421, h5, hlam]
                                          · linarith only [h2, h420, hlam]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          rcases p391_3 (m.d 0 1) (by simp) with h431 | h431
                                          · rcases p391_3 (m.d 0 2) (by simp) with h432 | h432
                                            · rcases p391_3 (m.d 0 3) (by simp) with h433 | h433
                                              · linarith only [h4, h433, hlam]
                                              · rcases p391_3 (m.d 0 4) (by simp) with h435 | h435
                                                · linarith only [h435, h5, hlam]
                                                · rcases p391_3 (m.d 0 5) (by simp) with h437 | h437
                                                  · linarith only [h437, h6, hlam]
                                                  · rcases h1bigk with h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h378, h386, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p439_1, u1elo0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      rcases p439_3 (m.d 0 1) (by simp) with h442 | h442
                                                      · rcases p439_3 (m.d 1 2) (by simp) with h443 | h443
                                                        · linarith only [h0, h443, hlam]
                                                        · linarith only [h377, h443, hlam]
                                                      · linarith only [h442, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      rcases p439_3 (m.d 0 1) (by simp) with h447 | h447
                                                      · rcases p439_3 (m.d 1 2) (by simp) with h448 | h448
                                                        · linarith only [h0, h448, hlam]
                                                        · linarith only [h378, h448, hlam]
                                                      · linarith only [h447, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      rcases p439_3 (m.d 0 1) (by simp) with h452 | h452
                                                      · rcases p439_3 (m.d 1 2) (by simp) with h453 | h453
                                                        · linarith only [h0, h453, hlam]
                                                        · linarith only [h379, h453, hlam]
                                                      · linarith only [h452, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h0, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h0, h377, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p439_1, u1elo0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h0, h377, h380, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p439_1, u1elo0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h0, h377, h380, h384, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p439_1, u1elo0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h1, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h377, hlam, p439_1]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h380, hlam, p439_1]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h382, hlam, p439_1]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h2, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h378, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h377, h384, hc23, hlam, hphi, ht34, ht45, p439_1, u5elo1]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h384, hlam, p439_1]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h3, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h379, hlam, p439_0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h3, h377, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p391_1, p439_1, u0elo1]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [h0, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p391_1, p439_1, u1elo0]
                                                    · obtain ⟨p439_0, p439_1, p439_2, p439_3⟩ := h439c
                                                      linarith only [hlam, p439_0]
                                            · linarith only [h432, h6, hlam]
                                          · linarith only [h3, h431, hlam]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h1, hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h4, hlam, p391_1]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h7, hlam, p391_1]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h141, hlam, p391_1]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h2, hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h5, hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h1, h202, h377, h390, hc23, hc34, hlam, hphi, p391_1]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h202, hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h3, hlam, p391_0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h6, hlam, p391_1]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h1, h377, hc23, hlam, hphi, ht34, ht45, p391_1, u5elo0]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [h202, h390, hc04, hlam, hphi, ht45, p391_1, u5elo3]
                                        · obtain ⟨p391_0, p391_1, p391_2, p391_3⟩ := h391c
                                          linarith only [hlam, p391_0]
                                      · linarith only [h1, h377, h390, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h377, h379, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h377, h378, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h141, h377, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h499 | h499
              · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
                · linarith only [h4, h5, h500, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                        · linarith only [h0, h5, h505, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                            · linarith only [h500, h502, h508, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                                  · linarith only [h0, h1, h500, h504, h510, h512, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h514 | h514
                                    · linarith only [h0, h504, h514, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h510, h514, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h505, h507, h511, hc25, hlam, hphi, u5elo4]
                              · linarith only [h500, h502, h510, hc13, hc34, hlam, hphi]
                          · linarith only [h504, h507, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h4, h5, h504, hc12, hc24, hlam, hphi]
                    · linarith only [h4, h5, h503, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                        · linarith only [h0, h5, h524, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                            · linarith only [h1, h502, h527, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                              · linarith only [h1, h502, h529, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h531 | h531
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                                  · linarith only [h0, h500, h523, h532, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h534 | h534
                                    · linarith only [h3, h502, h523, h529, h534, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                                      · rcases h0bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h0, h526, h534, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p537_1, u1elo0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          rcases p537_3 (m.d 0 1) (by simp) with h540 | h540
                                          · rcases p537_3 (m.d 0 2) (by simp) with h541 | h541
                                            · linarith only [h0, h541, hlam]
                                            · linarith only [h4, h541, hlam]
                                          · linarith only [h1, h540, hlam]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h0, h5, h526, h534, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p537_1, u1elo0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          rcases p537_3 (m.d 0 1) (by simp) with h546 | h546
                                          · rcases p537_3 (m.d 0 2) (by simp) with h547 | h547
                                            · linarith only [h0, h547, hlam]
                                            · linarith only [h499, h547, hlam]
                                          · linarith only [h3, h546, hlam]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h0, hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h1, h5, h532, hc13, hc34, hlam, hphi, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h5, hlam, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h499, h5, h532, h534, hc23, hc34, hlam, hphi, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h1, hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h4, hlam, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h500, hlam, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h502, hlam, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h2, hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h0, h526, h534, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u0elo3]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          rcases p537_3 (m.d 0 1) (by simp) with h563 | h563
                                          · rcases p537_3 (m.d 0 2) (by simp) with h564 | h564
                                            · linarith only [h5, h564, hlam]
                                            · linarith only [h4, h564, hlam]
                                          · linarith only [h1, h563, hlam]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          rcases p537_3 (m.d 0 1) (by simp) with h569 | h569
                                          · rcases p537_3 (m.d 0 2) (by simp) with h570 | h570
                                            · linarith only [h5, h570, hlam]
                                            · linarith only [h499, h570, hlam]
                                          · linarith only [h3, h569, hlam]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h3, hlam, p537_0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h499, hlam, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h1, h523, hc23, hlam, hphi, ht34, ht45, p537_1, u5elo0]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [h522, hlam, p537_1]
                                        · obtain ⟨p537_0, p537_1, p537_2, p537_3⟩ := h537c
                                          linarith only [hlam, p537_0]
                                      · linarith only [h5, h531, h532, h536, hc02, hlam, hphi, ht23, ht34, ht45, u5elo1]
                                · linarith only [h522, h523, h524, h531, hc23, hlam, hphi, ht34, ht45, u5elo0]
                          · linarith only [h523, h526, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h4, h5, h523, hc12, hc24, hlam, hphi]
                    · linarith only [h499, h5, h522, hc25, hlam, hphi, u5elo4]
              · linarith only [h4, h499, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h585 | h585
            · rcases m.htr 0 2 5 (by decide) (by decide) with h586 | h586
              · rcases m.htr 0 3 4 (by decide) (by decide) with h587 | h587
                · rcases m.htr 0 3 5 (by decide) (by decide) with h588 | h588
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h589 | h589
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
                      · linarith only [h4, h585, h590, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h592 | h592
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h596 | h596
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h597 | h597
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                                      · linarith only [h0, h592, h597, h599, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                      · linarith only [h1, h590, h592, h596, h599, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h4, h598, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h4, h587, h597, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h606 | h606
                                      · linarith only [h592, h596, h604, h606, hlam]
                                      · rcases h0bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h585, h589, h592, h596, h604, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h1, h590, h593, h605, h606, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h589, h592, h596, h604, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h589, h592, h596, h604, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h0, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h4, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h589, h592, h596, h604, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1, u0elo1]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h1, h4, h589, h592, h596, h604, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h1, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h0, h1, h593, h605, h606, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h1, h589, h592, h596, h604, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h1, h589, h592, h596, h604, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p608_1, u1elo0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h2, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h585, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h587, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h585, h589, h592, h596, h604, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1, u0elo1]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h3, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h586, hlam, p608_1]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h588, hlam, p608_0]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [h589, hlam, p608_1]
                                        · obtain ⟨p608_0, p608_1, p608_2, p608_3⟩ := h608c
                                          linarith only [hlam, p608_0]
                                    · linarith only [h4, h605, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h1, h594, h604, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h1, h588, h590, h592, h595, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h1, h587, h590, h592, h594, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h592, h593, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h4, h585, h592, hc12, hc23, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
                      · linarith only [h4, h585, h640, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h643 | h643
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h645 | h645
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h646 | h646
                                · linarith only [h2, h589, h646, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h648 | h648
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h649 | h649
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h650 | h650
                                      · linarith only [h1, h589, h640, h642, h648, h650, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · rcases h0bigk with h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h585, h648, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p652_1, u1elo0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h4, h585, h648, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p652_1, u1elo0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          rcases p652_3 (m.d 0 1) (by simp) with h656 | h656
                                          · rcases p652_3 (m.d 0 2) (by simp) with h657 | h657
                                            · linarith only [h0, h657, hlam]
                                            · linarith only [h585, h657, hlam]
                                          · linarith only [h2, h656, hlam]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          rcases p652_3 (m.d 0 1) (by simp) with h661 | h661
                                          · rcases p652_3 (m.d 0 2) (by simp) with h662 | h662
                                            · linarith only [h0, h662, hlam]
                                            · linarith only [h586, h662, hlam]
                                          · linarith only [h3, h661, hlam]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h0, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h4, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          rcases p652_3 (m.d 0 1) (by simp) with h669 | h669
                                          · rcases p652_3 (m.d 0 2) (by simp) with h670 | h670
                                            · rcases p652_3 (m.d 0 3) (by simp) with h671 | h671
                                              · rcases p652_3 (m.d 0 4) (by simp) with h672 | h672
                                                · linarith only [h585, h672, hlam]
                                                · rcases p652_3 (m.d 0 5) (by simp) with h674 | h674
                                                  · linarith only [h586, h674, hlam]
                                                  · linarith only [h589, h674, hlam]
                                              · linarith only [h587, h671, hlam]
                                            · linarith only [h585, h670, hlam]
                                          · linarith only [h2, h669, hlam]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          rcases p652_3 (m.d 0 1) (by simp) with h680 | h680
                                          · rcases p652_3 (m.d 0 2) (by simp) with h681 | h681
                                            · rcases p652_3 (m.d 0 3) (by simp) with h682 | h682
                                              · rcases p652_3 (m.d 0 4) (by simp) with h683 | h683
                                                · linarith only [h585, h683, hlam]
                                                · rcases p652_3 (m.d 0 5) (by simp) with h685 | h685
                                                  · linarith only [h586, h685, hlam]
                                                  · rcases h1bigk with h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h643, h649, h650, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h640, h643, h649, h650, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      rcases p687_3 (m.d 0 1) (by simp) with h691 | h691
                                                      · rcases p687_3 (m.d 1 2) (by simp) with h692 | h692
                                                        · linarith only [h0, h692, hlam]
                                                        · linarith only [h642, h692, hlam]
                                                      · linarith only [h691, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      rcases p687_3 (m.d 0 1) (by simp) with h696 | h696
                                                      · rcases p687_3 (m.d 1 2) (by simp) with h697 | h697
                                                        · linarith only [h0, h697, hlam]
                                                        · linarith only [h643, h697, hlam]
                                                      · linarith only [h696, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h0, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h640, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h0, h642, h648, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h1, h640, hc15, hlam, hphi, ht01, ht0b, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h1, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h1, h642, h648, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h1, h643, h649, h650, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p687_1, u1elo0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h2, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h642, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h644, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h646, hlam, p687_1]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h3, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h643, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h645, hlam, p687_0]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [h642, h648, hc34, hlam, hphi, ht45, p687_1, u5elo1]
                                                    · obtain ⟨p687_0, p687_1, p687_2, p687_3⟩ := h687c
                                                      linarith only [hlam, p687_0]
                                              · linarith only [h588, h682, hlam]
                                            · linarith only [h586, h681, hlam]
                                          · linarith only [h3, h680, hlam]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h1, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h0, h643, h649, h650, hc34, hlam, hphi, ht0b, ht45, ht5b, p652_1, u0elo2]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          rcases p652_3 (m.d 0 1) (by simp) with h727 | h727
                                          · rcases p652_3 (m.d 0 2) (by simp) with h728 | h728
                                            · linarith only [h4, h728, hlam]
                                            · linarith only [h585, h728, hlam]
                                          · linarith only [h2, h727, hlam]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          rcases p652_3 (m.d 0 1) (by simp) with h732 | h732
                                          · rcases p652_3 (m.d 0 2) (by simp) with h733 | h733
                                            · linarith only [h4, h733, hlam]
                                            · linarith only [h586, h733, hlam]
                                          · linarith only [h3, h732, hlam]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h2, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h585, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h587, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h589, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h3, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h586, hlam, p652_1]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h588, hlam, p652_0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [h2, h642, h648, hc34, hlam, hphi, ht45, p652_1, u5elo0]
                                        · obtain ⟨p652_0, p652_1, p652_2, p652_3⟩ := h652c
                                          linarith only [hlam, p652_0]
                                    · linarith only [h4, h649, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h4, h587, h648, hlam]
                              · linarith only [h588, h640, h642, h645, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1, h587, h640, h642, h644, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h642, h643, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h4, h585, h642, hc12, hc23, hlam, hphi]
                  · linarith only [h4, h585, h588, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h4, h585, h587, hlam]
              · linarith only [h585, h586, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h756 | h756
              · rcases m.htr 0 3 4 (by decide) (by decide) with h757 | h757
                · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                      · linarith only [h4, h756, h760, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
                        · linarith only [h0, h585, h762, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h764 | h764
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h765 | h765
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h766 | h766
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h767 | h767
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h768 | h768
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h769 | h769
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h770 | h770
                                      · linarith only [h1, h765, h770, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                      · linarith only [h2, h767, h770, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h0, h4, h764, h769, hc25, hlam, hphi, u5elo3]
                                  · linarith only [h4, h757, h768, hlam]
                                · linarith only [h762, h764, h767, hc25, hlam, hphi, u5elo4]
                              · linarith only [h765, h766, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h757, h760, h764, h765, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h585, h756, h764, hc12, hc24, hlam, hphi]
                    · linarith only [h585, h756, h759, hc25, hlam, hphi, u5elo4]
                  · linarith only [h4, h756, h758, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h782 | h782
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                      · linarith only [h4, h756, h783, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
                        · linarith only [h0, h585, h785, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h787 | h787
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h788 | h788
                            · linarith only [h757, h781, h788, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h790 | h790
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h791 | h791
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h792 | h792
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h793 | h793
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h794 | h794
                                      · rcases h0bigk with h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h0, h787, h793, h794, hc45, hlam, hphi, ht01, ht0b, ht5b, p795_1, u1elo0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h0, h4, h787, h793, h794, hc45, hlam, hphi, ht01, ht0b, ht5b, p795_1, u1elo0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h0, h4, h757, h787, h793, h794, hc45, hlam, hphi, ht01, ht0b, ht5b, p795_1, u1elo0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          rcases p795_3 (m.d 0 1) (by simp) with h800 | h800
                                          · rcases p795_3 (m.d 0 2) (by simp) with h801 | h801
                                            · linarith only [h0, h801, hlam]
                                            · linarith only [h756, h801, hlam]
                                          · linarith only [h3, h800, hlam]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h0, hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h4, hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h585, hlam, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h4, h757, h792, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h1, hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h757, h792, hc02, hc23, hlam, hphi, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h757, hlam, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h756, h757, h792, h793, h794, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h2, hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h0, h787, h793, h794, hc45, hlam, hphi, ht0b, ht5b, p795_1, u0elo3]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h1, h757, h783, h787, h792, h793, h794, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          rcases p795_3 (m.d 0 1) (by simp) with h819 | h819
                                          · rcases p795_3 (m.d 0 2) (by simp) with h820 | h820
                                            · linarith only [h585, h820, hlam]
                                            · linarith only [h756, h820, hlam]
                                          · linarith only [h3, h819, hlam]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h3, hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h756, hlam, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h781, hlam, p795_0]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [h782, hlam, p795_1]
                                        · obtain ⟨p795_0, p795_1, p795_2, p795_3⟩ := h795c
                                          linarith only [hlam, p795_0]
                                      · linarith only [h0, h585, h757, h787, h794, hc25, hlam, hphi, u5elo4]
                                    · linarith only [h0, h4, h787, h793, hc25, hlam, hphi, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h831 | h831
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
                                      · rcases h0bigk with h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h0, h787, h831, h832, hc45, hlam, hphi, ht0b, ht5b, p833_1, u0elo0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h0, h4, h787, h831, h832, hc45, hlam, hphi, ht01, ht0b, ht5b, p833_1, u1elo0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h0, h4, h757, h787, h831, h832, hc45, hlam, hphi, ht01, ht0b, ht5b, p833_1, u1elo0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          rcases p833_3 (m.d 0 1) (by simp) with h838 | h838
                                          · rcases p833_3 (m.d 0 2) (by simp) with h839 | h839
                                            · linarith only [h0, h839, hlam]
                                            · linarith only [h756, h839, hlam]
                                          · linarith only [h3, h838, hlam]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h0, hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h4, hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h585, hlam, p833_1]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h3, h4, h787, h792, h831, h832, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p833_1]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h1, hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h0, h757, h787, h831, h832, hc45, hlam, hphi, ht0b, ht5b, p833_1, u0elo3]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h757, hlam, p833_1]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          rcases p833_3 (m.d 0 1) (by simp) with h852 | h852
                                          · rcases p833_3 (m.d 0 2) (by simp) with h853 | h853
                                            · linarith only [h4, h853, hlam]
                                            · linarith only [h756, h853, hlam]
                                          · linarith only [h3, h852, hlam]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h2, hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h0, h2, h787, h831, h832, hc45, hlam, hphi, ht01, ht0b, ht5b, p833_1, u1elo0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h1, h2, h783, h787, h831, h832, hc45, hlam, hphi, ht01, ht0b, ht5b, p833_1, u1elo0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          rcases p833_3 (m.d 0 1) (by simp) with h861 | h861
                                          · rcases p833_3 (m.d 0 2) (by simp) with h862 | h862
                                            · linarith only [h585, h862, hlam]
                                            · linarith only [h756, h862, hlam]
                                          · linarith only [h3, h861, hlam]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h3, hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h756, hlam, p833_1]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h781, hlam, p833_0]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [h782, hlam, p833_1]
                                        · obtain ⟨p833_0, p833_1, p833_2, p833_3⟩ := h833c
                                          linarith only [hlam, p833_0]
                                      · linarith only [h0, h4, h787, h792, h831, h832, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h0, h4, h787, h831, hc25, hlam, hphi, u5elo3]
                                · linarith only [h783, h787, h788, h791, hc25, hlam, hphi, u5elo4]
                              · linarith only [h783, h787, h790, hc25, hlam, hphi, u5elo3]
                          · linarith only [h4, h756, h787, hc12, hc23, hlam, hphi]
                    · linarith only [h585, h756, h782, hc25, hlam, hphi, u5elo4]
                  · linarith only [h4, h756, h781, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h878 | h878
                · rcases m.htr 0 3 5 (by decide) (by decide) with h879 | h879
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h880 | h880
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h881 | h881
                      · linarith only [h0, h756, h881, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h883 | h883
                        · linarith only [h0, h585, h883, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h885 | h885
                          · linarith only [h0, h756, h885, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h887 | h887
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h888 | h888
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h889 | h889
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h892 | h892
                                      · linarith only [h1, h887, h892, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                      · linarith only [h2, h889, h892, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h585, h890, h891, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h4, h878, h890, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h897 | h897
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h898 | h898
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h899 | h899
                                      · linarith only [h887, h889, h899, hlam]
                                      · rcases h0bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          rcases p901_3 (m.d 0 1) (by simp) with h903 | h903
                                          · rcases p901_3 (m.d 0 2) (by simp) with h904 | h904
                                            · linarith only [h0, h904, hlam]
                                            · rcases p901_3 (m.d 0 3) (by simp) with h906 | h906
                                              · linarith only [h1, h906, hlam]
                                              · linarith only [h4, h906, hlam]
                                          · linarith only [h0, h903, hlam]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h878, h880, h883, h889, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p901_1, u1elo0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h880, h883, h889, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p901_1, u1elo0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h880, h883, h889, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p901_1, u1elo0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h0, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h4, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h585, hlam, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h756, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h1, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          rcases p901_3 (m.d 0 1) (by simp) with h919 | h919
                                          · rcases p901_3 (m.d 0 2) (by simp) with h920 | h920
                                            · linarith only [h4, h920, hlam]
                                            · rcases p901_3 (m.d 0 3) (by simp) with h922 | h922
                                              · rcases p901_3 (m.d 0 4) (by simp) with h923 | h923
                                                · linarith only [h878, h923, hlam]
                                                · linarith only [h585, h923, hlam]
                                              · linarith only [h4, h922, hlam]
                                          · linarith only [h0, h919, hlam]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h880, h883, h889, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p901_1, u0elo2]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h1, h880, h883, h889, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p901_1, u1elo0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h2, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          rcases p901_3 (m.d 0 1) (by simp) with h932 | h932
                                          · rcases p901_3 (m.d 0 2) (by simp) with h933 | h933
                                            · linarith only [h585, h933, hlam]
                                            · rcases p901_3 (m.d 0 3) (by simp) with h935 | h935
                                              · rcases p901_3 (m.d 0 4) (by simp) with h936 | h936
                                                · rcases p901_3 (m.d 0 5) (by simp) with h937 | h937
                                                  · linarith only [h880, h937, hlam]
                                                  · linarith only [h756, h937, hlam]
                                                · linarith only [h585, h936, hlam]
                                              · linarith only [h4, h935, hlam]
                                          · linarith only [h0, h932, hlam]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h878, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h880, h883, h889, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p901_1, u0elo3]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h3, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p901_1, u5elo0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h879, hlam, p901_0]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [h880, hlam, p901_1]
                                        · obtain ⟨p901_0, p901_1, p901_2, p901_3⟩ := h901c
                                          linarith only [hlam, p901_0]
                                    · linarith only [h1, h4, h888, h898, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h4, h878, h880, h887, h889, h897, hlam]
                              · linarith only [h1, h879, h887, h888, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h954 | h954
                              · linarith only [h1, h878, h887, h954, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h956 | h956
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h958 | h958
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h959 | h959
                                      · rcases h0bigk with h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          rcases p960_3 (m.d 0 1) (by simp) with h962 | h962
                                          · rcases p960_3 (m.d 0 2) (by simp) with h963 | h963
                                            · linarith only [h0, h963, hlam]
                                            · rcases p960_3 (m.d 0 3) (by simp) with h965 | h965
                                              · linarith only [h1, h965, hlam]
                                              · linarith only [h4, h965, hlam]
                                          · linarith only [h0, h962, hlam]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h878, h887, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p960_1, u1elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h879, h880, h954, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p960_1, u1elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h879, h954, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p960_1, u1elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h0, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h4, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h585, hlam, p960_1]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h756, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h1, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          rcases p960_3 (m.d 0 1) (by simp) with h978 | h978
                                          · rcases p960_3 (m.d 0 2) (by simp) with h979 | h979
                                            · linarith only [h4, h979, hlam]
                                            · rcases p960_3 (m.d 0 3) (by simp) with h981 | h981
                                              · rcases p960_3 (m.d 0 4) (by simp) with h982 | h982
                                                · linarith only [h878, h982, hlam]
                                                · linarith only [h585, h982, hlam]
                                              · linarith only [h4, h981, hlam]
                                          · linarith only [h0, h978, hlam]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h1, h879, h880, h881, h954, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p960_1, u1elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h1, h879, h881, h954, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p960_1, u1elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h2, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          rcases p960_3 (m.d 0 1) (by simp) with h991 | h991
                                          · rcases p960_3 (m.d 0 2) (by simp) with h992 | h992
                                            · linarith only [h585, h992, hlam]
                                            · rcases p960_3 (m.d 0 3) (by simp) with h994 | h994
                                              · rcases p960_3 (m.d 0 4) (by simp) with h995 | h995
                                                · rcases p960_3 (m.d 0 5) (by simp) with h996 | h996
                                                  · linarith only [h880, h996, hlam]
                                                  · linarith only [h756, h996, hlam]
                                                · linarith only [h585, h995, hlam]
                                              · linarith only [h4, h994, hlam]
                                          · linarith only [h0, h991, hlam]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h878, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h1, h878, h879, h881, h954, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p960_1, u1elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h3, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p960_1, u5elo0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h879, hlam, p960_0]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [h880, hlam, p960_1]
                                        · obtain ⟨p960_0, p960_1, p960_2, p960_3⟩ := h960c
                                          linarith only [hlam, p960_0]
                                      · linarith only [h1, h878, h880, h881, h887, h959, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                    · linarith only [h2, h4, h878, h956, h958, hc45, hlam, hphi, u5elo3]
                                  · linarith only [h4, h878, h957, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1014 | h1014
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1015 | h1015
                                      · linarith only [h1, h1015, h878, h956, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · linarith only [h1015, h880, h881, h887, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                                    · linarith only [h1014, h4, h878, h880, hc45, hlam, hphi, u5elo3]
                                  · linarith only [h1013, h4, h878, h880, h881, h887, h956, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                      · linarith only [h0, h1020, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1022 | h1022
                        · linarith only [h0, h1022, h585, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1024 | h1024
                          · linarith only [h0, h1024, h585, h880, hc25, hlam, hphi, u5elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1027 | h1027
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1028 | h1028
                                · linarith only [h1028, h2, h585, h880, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1030 | h1030
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1031 | h1031
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1032 | h1032
                                      · linarith only [h0, h1026, h1032, h585, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                      · rcases h0bigk with h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          rcases p1034_3 (m.d 0 1) (by simp) with h1036 | h1036
                                          · rcases p1034_3 (m.d 0 2) (by simp) with h1037 | h1037
                                            · linarith only [h0, h1037, hlam]
                                            · rcases p1034_3 (m.d 0 3) (by simp) with h1039 | h1039
                                              · linarith only [h1, h1039, hlam]
                                              · linarith only [h1039, h4, hlam]
                                          · linarith only [h0, h1036, hlam]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h878, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1034_1, u1elo0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          rcases p1034_3 (m.d 0 1) (by simp) with h1044 | h1044
                                          · rcases p1034_3 (m.d 0 2) (by simp) with h1045 | h1045
                                            · linarith only [h0, h1045, hlam]
                                            · rcases p1034_3 (m.d 0 3) (by simp) with h1047 | h1047
                                              · linarith only [h1, h1047, hlam]
                                              · linarith only [h1047, h878, hlam]
                                          · linarith only [h1044, h2, hlam]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          rcases p1034_3 (m.d 0 1) (by simp) with h1051 | h1051
                                          · rcases p1034_3 (m.d 0 2) (by simp) with h1052 | h1052
                                            · linarith only [h0, h1052, hlam]
                                            · rcases p1034_3 (m.d 0 3) (by simp) with h1054 | h1054
                                              · linarith only [h1, h1054, hlam]
                                              · linarith only [h1054, h879, hlam]
                                          · linarith only [h1051, h3, hlam]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h0, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h4, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h585, hlam, p1034_1]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h756, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h1, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          rcases p1034_3 (m.d 0 1) (by simp) with h1064 | h1064
                                          · rcases p1034_3 (m.d 0 2) (by simp) with h1065 | h1065
                                            · linarith only [h1065, h4, hlam]
                                            · rcases p1034_3 (m.d 0 3) (by simp) with h1067 | h1067
                                              · rcases p1034_3 (m.d 0 4) (by simp) with h1068 | h1068
                                                · linarith only [h1068, h878, hlam]
                                                · linarith only [h1068, h585, hlam]
                                              · linarith only [h1067, h4, hlam]
                                          · linarith only [h0, h1064, hlam]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          rcases p1034_3 (m.d 0 1) (by simp) with h1074 | h1074
                                          · rcases p1034_3 (m.d 0 2) (by simp) with h1075 | h1075
                                            · linarith only [h1075, h4, hlam]
                                            · rcases p1034_3 (m.d 0 3) (by simp) with h1077 | h1077
                                              · rcases p1034_3 (m.d 0 4) (by simp) with h1078 | h1078
                                                · linarith only [h1078, h878, hlam]
                                                · rcases p1034_3 (m.d 0 5) (by simp) with h1080 | h1080
                                                  · linarith only [h1080, h879, hlam]
                                                  · linarith only [h1080, h880, hlam]
                                              · linarith only [h1077, h878, hlam]
                                          · linarith only [h1074, h2, hlam]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          rcases p1034_3 (m.d 0 1) (by simp) with h1085 | h1085
                                          · rcases p1034_3 (m.d 0 2) (by simp) with h1086 | h1086
                                            · linarith only [h1086, h4, hlam]
                                            · rcases p1034_3 (m.d 0 3) (by simp) with h1088 | h1088
                                              · rcases p1034_3 (m.d 0 4) (by simp) with h1089 | h1089
                                                · linarith only [h1089, h878, hlam]
                                                · rcases p1034_3 (m.d 0 5) (by simp) with h1091 | h1091
                                                  · linarith only [h1091, h879, hlam]
                                                  · rcases h1bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      rcases p1093_3 (m.d 0 1) (by simp) with h1095 | h1095
                                                      · rcases p1093_3 (m.d 1 2) (by simp) with h1096 | h1096
                                                        · linarith only [h1096, hlam, p1093_0]
                                                        · rcases p1093_3 (m.d 1 3) (by simp) with h1098 | h1098
                                                          · linarith only [h1, h1098, hlam]
                                                          · linarith only [h1020, h1098, hlam]
                                                      · linarith only [h1095, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1027, h1032, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1093_1, u1elo0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      rcases p1093_3 (m.d 0 1) (by simp) with h1103 | h1103
                                                      · rcases p1093_3 (m.d 1 2) (by simp) with h1104 | h1104
                                                        · linarith only [h0, h1104, hlam]
                                                        · rcases p1093_3 (m.d 1 3) (by simp) with h1106 | h1106
                                                          · linarith only [h1, h1106, hlam]
                                                          · linarith only [h1026, h1106, hlam]
                                                      · linarith only [h1103, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      rcases p1093_3 (m.d 0 1) (by simp) with h1110 | h1110
                                                      · rcases p1093_3 (m.d 1 2) (by simp) with h1111 | h1111
                                                        · linarith only [h0, h1111, hlam]
                                                        · rcases p1093_3 (m.d 1 3) (by simp) with h1113 | h1113
                                                          · linarith only [h1, h1113, hlam]
                                                          · linarith only [h1027, h1113, hlam]
                                                      · linarith only [h1110, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h0, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1020, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1022, hlam, p1093_1]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1024, hlam, p1093_1]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1093_1, u1elo0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1093_1, u1elo0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1093_1, u1elo0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h2, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1093_1, u1elo0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1026, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1028, hlam, p1093_1]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h3, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1093_1, u5elo1]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h1027, hlam, p1093_0]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p1034_1, p1093_1, u0elo2]
                                                    · obtain ⟨p1093_0, p1093_1, p1093_2, p1093_3⟩ := h1093c
                                                      linarith only [hlam, p1093_0]
                                              · linarith only [h1088, h879, hlam]
                                          · linarith only [h1085, h3, hlam]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h2, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h0, h880, hc12, hc45, hlam, hphi, ht23, ht34, p1034_1]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h878, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h880, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h3, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h0, h756, hc12, hlam, hphi, ht23, ht34, ht45, p1034_1, u5elo2]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h879, hlam, p1034_0]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [h756, hc04, hlam, hphi, ht45, p1034_1, u5elo2]
                                        · obtain ⟨p1034_0, p1034_1, p1034_2, p1034_3⟩ := h1034c
                                          linarith only [hlam, p1034_0]
                                    · linarith only [h0, h1031, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h0, h1, h1026, h1030, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1, h1026, h1027, h879, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h1026, h878, h880, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h878, h879, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1154 | h1154
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1155 | h1155
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1156 | h1156
                      · linarith only [h0, h1156, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
                        · linarith only [h0, h1158, h585, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1160 | h1160
                          · linarith only [h0, h1160, h756, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1162 | h1162
                            · linarith only [h1, h1162, h878, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1164 | h1164
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1165 | h1165
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1166 | h1166
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1167 | h1167
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1168 | h1168
                                      · rcases h0bigk with h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c | h1169c
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          rcases p1169_3 (m.d 0 1) (by simp) with h1171 | h1171
                                          · rcases p1169_3 (m.d 0 2) (by simp) with h1172 | h1172
                                            · linarith only [h0, h1172, hlam]
                                            · rcases p1169_3 (m.d 0 3) (by simp) with h1174 | h1174
                                              · linarith only [h1, h1174, hlam]
                                              · linarith only [h1174, h4, hlam]
                                          · linarith only [h0, h1171, hlam]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1, h1164, h1168, hc45, hlam, hphi, ht01, ht0b, ht5b, p1169_1, u1elo0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1, h1164, h1168, h878, hc45, hlam, hphi, ht01, ht0b, ht5b, p1169_1, u1elo0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          rcases p1169_3 (m.d 0 1) (by simp) with h1180 | h1180
                                          · rcases p1169_3 (m.d 0 2) (by simp) with h1181 | h1181
                                            · linarith only [h0, h1181, hlam]
                                            · rcases p1169_3 (m.d 0 3) (by simp) with h1183 | h1183
                                              · linarith only [h1, h1183, hlam]
                                              · linarith only [h1154, h1183, hlam]
                                          · linarith only [h1180, h3, hlam]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h0, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h4, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h585, hlam, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h756, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h0, h1166, h878, hc12, hc23, hlam, hphi, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h878, hlam, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1166, h878, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h2, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h0, h1166, h878, hc12, hc23, hlam, hphi, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1, h1164, h1166, h1168, h878, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h0, h1166, h756, h878, hc12, hc23, hlam, hphi, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h3, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1169_1, u5elo0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1154, hlam, p1169_0]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [h1155, hlam, p1169_1]
                                        · obtain ⟨p1169_0, p1169_1, p1169_2, p1169_3⟩ := h1169c
                                          linarith only [hlam, p1169_0]
                                      · linarith only [h1168, h878, hc03, hlam, hphi, ht34, ht45, u5elo4]
                                    · linarith only [h1, h1164, h1167, h878, hc23, hc34, hlam, hphi]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1209 | h1209
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1210 | h1210
                                      · rcases h0bigk with h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          rcases p1211_3 (m.d 0 1) (by simp) with h1213 | h1213
                                          · rcases p1211_3 (m.d 0 2) (by simp) with h1214 | h1214
                                            · linarith only [h0, h1214, hlam]
                                            · rcases p1211_3 (m.d 0 3) (by simp) with h1216 | h1216
                                              · linarith only [h1, h1216, hlam]
                                              · linarith only [h1216, h4, hlam]
                                          · linarith only [h0, h1213, hlam]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h1, h1164, hc35, hlam, hphi, ht01, ht0b, ht5b, p1211_1, u1elo0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h1, h1164, h1210, h878, hc45, hlam, hphi, ht01, ht0b, ht5b, p1211_1, u1elo0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          rcases p1211_3 (m.d 0 1) (by simp) with h1222 | h1222
                                          · rcases p1211_3 (m.d 0 2) (by simp) with h1223 | h1223
                                            · linarith only [h0, h1223, hlam]
                                            · rcases p1211_3 (m.d 0 3) (by simp) with h1225 | h1225
                                              · linarith only [h1, h1225, hlam]
                                              · linarith only [h1154, h1225, hlam]
                                          · linarith only [h1222, h3, hlam]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h0, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h4, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h585, hlam, p1211_1]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h756, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h1, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h0, h1166, h4, hc12, hc34, hlam, hphi, ht23, p1211_1]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h878, hlam, p1211_1]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h0, h1166, h4, h756, hc12, hc34, hlam, hphi, ht23, p1211_1]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h2, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          rcases p1211_3 (m.d 0 1) (by simp) with h1240 | h1240
                                          · rcases p1211_3 (m.d 0 2) (by simp) with h1241 | h1241
                                            · linarith only [h1241, h585, hlam]
                                            · rcases p1211_3 (m.d 0 3) (by simp) with h1243 | h1243
                                              · linarith only [h1243, h878, hlam]
                                              · linarith only [h1243, h4, hlam]
                                          · linarith only [h0, h1240, hlam]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h1, h1164, h1210, hc45, hlam, hphi, ht0b, ht5b, p1211_1, u0elo3]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          rcases p1211_3 (m.d 0 1) (by simp) with h1249 | h1249
                                          · rcases p1211_3 (m.d 0 2) (by simp) with h1250 | h1250
                                            · linarith only [h1250, h585, hlam]
                                            · rcases p1211_3 (m.d 0 3) (by simp) with h1252 | h1252
                                              · linarith only [h1252, h878, hlam]
                                              · linarith only [h1154, h1252, hlam]
                                          · linarith only [h1249, h3, hlam]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h3, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1211_1, u5elo0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h1154, hlam, p1211_0]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [h1155, hlam, p1211_1]
                                        · obtain ⟨p1211_0, p1211_1, p1211_2, p1211_3⟩ := h1211c
                                          linarith only [hlam, p1211_0]
                                      · linarith only [h1166, h1210, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                    · linarith only [h1, h1164, h1209, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h1155, h1162, h1164, h1165, hc35, hlam, hphi, u5elo0]
                              · linarith only [h1154, h1164, h878, hc13, hc34, hlam, hphi]
                    · linarith only [h1154, h1155, h878, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1266 | h1266
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1267 | h1267
                      · linarith only [h0, h1267, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1269 | h1269
                        · linarith only [h0, h1269, h585, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1271 | h1271
                          · linarith only [h1, h1154, h1267, h1271, hc25, hlam, hphi, u5elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1273 | h1273
                            · linarith only [h1, h1154, h1273, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1275 | h1275
                              · linarith only [h1, h1154, h1275, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1277 | h1277
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1280 | h1280
                                      · rcases h0bigk with h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          rcases p1281_3 (m.d 0 1) (by simp) with h1283 | h1283
                                          · rcases p1281_3 (m.d 0 2) (by simp) with h1284 | h1284
                                            · linarith only [h0, h1284, hlam]
                                            · rcases p1281_3 (m.d 0 3) (by simp) with h1286 | h1286
                                              · linarith only [h1, h1286, hlam]
                                              · linarith only [h1286, h4, hlam]
                                          · linarith only [h0, h1283, hlam]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          rcases p1281_3 (m.d 0 1) (by simp) with h1290 | h1290
                                          · rcases p1281_3 (m.d 0 2) (by simp) with h1291 | h1291
                                            · linarith only [h0, h1291, hlam]
                                            · rcases p1281_3 (m.d 0 3) (by simp) with h1293 | h1293
                                              · linarith only [h1, h1293, hlam]
                                              · rcases p1281_3 (m.d 0 4) (by simp) with h1295 | h1295
                                                · linarith only [h1295, h2, hlam]
                                                · linarith only [h1295, h878, hlam]
                                          · linarith only [h1, h1290, hlam]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h1277, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1281_1, u1elo0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          rcases p1281_3 (m.d 0 1) (by simp) with h1300 | h1300
                                          · rcases p1281_3 (m.d 0 2) (by simp) with h1301 | h1301
                                            · linarith only [h0, h1301, hlam]
                                            · rcases p1281_3 (m.d 0 3) (by simp) with h1303 | h1303
                                              · linarith only [h1, h1303, hlam]
                                              · rcases p1281_3 (m.d 0 4) (by simp) with h1305 | h1305
                                                · linarith only [h1305, h2, hlam]
                                                · linarith only [h1266, h1305, hlam]
                                          · linarith only [h1300, h3, hlam]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h0, hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h4, hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h585, hlam, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h756, hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h1, hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h1154, h1278, h1280, hc02, hc23, hlam, hphi, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h878, hlam, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h1154, hlam, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h2, hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h0, h1278, h878, hc12, hc23, hlam, hphi, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h0, h1278, h4, h878, hc12, hc23, hlam, hphi, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h0, h1154, h1278, h4, h878, hc12, hc23, hlam, hphi, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h3, hlam, p1281_0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1281_1, u5elo0]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h0, h1154, h1279, h4, hc12, hlam, hphi, ht23, ht34, ht45, p1281_1, u5elo2]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [h1266, hlam, p1281_1]
                                        · obtain ⟨p1281_0, p1281_1, p1281_2, p1281_3⟩ := h1281c
                                          linarith only [hlam, p1281_0]
                                      · linarith only [h1277, h1280, h2, h878, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h0, h1279, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1331 | h1331
                                    · linarith only [h0, h1154, h1278, h1331, h4, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h1331, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1334 | h1334
                                  · linarith only [h1266, h1267, h1273, h1277, h1334, h878, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1336 | h1336
                                    · linarith only [h0, h1154, h1334, h1336, h4, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h1336, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1339 | h1339
                      · linarith only [h0, h1339, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
                        · linarith only [h0, h1341, h585, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1343 | h1343
                          · linarith only [h0, h1266, h1343, h4, h756, h878, hc05, hlam, hphi, u5elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1345 | h1345
                            · linarith only [h1, h1266, h1345, h878, hc34, hlam, hphi, ht45, u5elo4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1347 | h1347
                              · linarith only [h1, h1266, h1347, h878, hc35, hlam, hphi, u5elo4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1349 | h1349
                                · linarith only [h0, h1266, h1349, h2, h4, h878, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1351 | h1351
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1352 | h1352
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1353 | h1353
                                      · linarith only [h0, h1266, h1351, h1353, h4, h878, hc12, hc23, hlam, hphi]
                                      · linarith only [h0, h1353, h4, h878, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                    · linarith only [h0, h1352, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1357 | h1357
                                    · linarith only [h0, h1154, h1351, h1357, h4, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h1357, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1361 | h1361
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1362 | h1362
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1363 | h1363
            · linarith only [h0, h1363, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1365 | h1365
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1366 | h1366
                · linarith only [h1, h1366, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1368 | h1368
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1369 | h1369
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1370 | h1370
                      · linarith only [h0, h1370, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · linarith only [h0, h1362, h1370, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h1362, h1369, h2, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1374 | h1374
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1375 | h1375
                      · linarith only [h0, h1375, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · linarith only [h0, h1362, h1375, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h1, h1374, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h1362, h1365, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1380 | h1380
            · linarith only [h1, h1362, h1380, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1382 | h1382
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1383 | h1383
                · linarith only [h1, h1383, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1385 | h1385
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1386 | h1386
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1387 | h1387
                      · linarith only [h0, h1362, h1387, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1389 | h1389
                        · linarith only [h1, h1380, h1387, h1389, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1391 | h1391
                          · linarith only [h1, h1387, h1391, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                          · linarith only [h1362, h1382, h1391, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h1386, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1362, h1382, h1385, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1396 | h1396
                · linarith only [h1, h1396, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1398 | h1398
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1399 | h1399
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1400 | h1400
                      · linarith only [h0, h1362, h1400, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1402 | h1402
                        · linarith only [h0, h1380, h1402, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1404 | h1404
                          · linarith only [h1, h1400, h1404, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1406 | h1406
                            · linarith only [h1, h1396, h1406, h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1408 | h1408
                              · linarith only [h1, h1408, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                              · linarith only [h1, h1398, h1400, h1408, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h1399, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1412 | h1412
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1413 | h1413
                      · linarith only [h0, h1362, h1413, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1415 | h1415
                        · linarith only [h0, h1382, h1415, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
                          · linarith only [h0, h1382, h1417, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1419 | h1419
                            · linarith only [h1, h1419, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1421 | h1421
                              · linarith only [h1, h1362, h1398, h1421, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1423 | h1423
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1424 | h1424
                                  · linarith only [h0, h1419, h1424, h2, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1426 | h1426
                                    · linarith only [h0, h1362, h1398, h1424, h1426, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h0, h1362, h1426, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                · linarith only [h1361, h1413, h1421, h1423, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1361, h1412, h2, hc15, hlam, hphi, u5elo4]
        · linarith only [h1, h1361, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1432 | h1432
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1433 | h1433
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1434 | h1434
          · linarith only [h0, h1, h1434, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1436 | h1436
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1437 | h1437
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1438 | h1438
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1439 | h1439
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1440 | h1440
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
                      · linarith only [h0, h1434, h1441, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1443 | h1443
                        · linarith only [h0, h1, h1443, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h1436, h1443, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
                      · linarith only [h0, h1, h1446, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1448 | h1448
                        · linarith only [h0, h1, h1448, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h1436, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1, h1439, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h1, h1432, h1438, hlam]
              · linarith only [h1436, h1437, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1454 | h1454
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1455 | h1455
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1456 | h1456
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1457 | h1457
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1458 | h1458
                      · linarith only [h0, h1434, h1454, h1458, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1460 | h1460
                        · linarith only [h0, h1, h1436, h1454, h1460, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1462 | h1462
                          · linarith only [h1, h1432, h1460, h1462, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · linarith only [h1436, h1454, h1462, hc12, hc24, hlam, hphi]
                    · linarith only [h1436, h1454, h1457, hc25, hlam, hphi, u5elo4]
                  · linarith only [h1, h1432, h1456, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h1, h1432, h1455, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1468 | h1468
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1469 | h1469
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1471 | h1471
                      · linarith only [h0, h1434, h1471, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1473 | h1473
                        · linarith only [h0, h1, h1473, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1475 | h1475
                          · linarith only [h1, h1432, h1473, h1475, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1477 | h1477
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1478 | h1478
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1479 | h1479
                                · linarith only [h1, h1432, h1479, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                                · linarith only [h1, h1432, h1470, h1473, h1479, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h1, h1469, h1478, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                            · linarith only [h1, h1432, h1468, h1477, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1484 | h1484
                      · linarith only [h0, h1, h1484, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1486 | h1486
                        · linarith only [h0, h1, h1436, h1486, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1488 | h1488
                          · linarith only [h0, h1, h1488, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1490 | h1490
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1491 | h1491
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1492 | h1492
                                · linarith only [h1, h1432, h1436, h1470, h1492, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1494 | h1494
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1495 | h1495
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1496 | h1496
                                      · linarith only [h1, h1432, h1470, h1490, h1496, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                                      · rcases h0bigk with h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c | h1498c
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1498_1, u1elo2]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1, hlam, p1498_1]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p1498_1, u1elo2]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1, h1432, h1470, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1498_1, u1elo2]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h0, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1434, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1436, hlam, p1498_1]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1454, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1, hc01, hlam, hphi, p1498_1, u1elo2]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          rcases p1498_3 (m.d 0 1) (by simp) with h1510 | h1510
                                          · linarith only [h1, h1510, hlam]
                                          · linarith only [h0, h1510, hlam]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          rcases p1498_3 (m.d 0 1) (by simp) with h1514 | h1514
                                          · linarith only [h1, h1514, hlam]
                                          · linarith only [h1432, h1514, hlam]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          rcases p1498_3 (m.d 0 1) (by simp) with h1517 | h1517
                                          · linarith only [h1, h1517, hlam]
                                          · linarith only [h1433, h1517, hlam]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1432, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h0, h1470, hc12, hc45, hlam, hphi, ht23, ht34, p1498_1]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1468, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1470, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1433, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1498_1, u5elo0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1469, hlam, p1498_0]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [h1, h1433, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p1498_1, u1elo2]
                                        · obtain ⟨p1498_0, p1498_1, p1498_2, p1498_3⟩ := h1498c
                                          linarith only [hlam, p1498_0]
                                    · linarith only [h1, h1484, h1495, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h1, h1433, h1484, h1486, h1492, h1494, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h1, h1491, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1, h1433, h1468, h1490, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h0, h1, h1469, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h1, h1432, h1468, hlam]
        · linarith only [h0, h1433, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1537 | h1537
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1538 | h1538
          · linarith only [h0, h1, h1538, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1540 | h1540
            · linarith only [h0, h1432, h1540, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1542 | h1542
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1543 | h1543
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1544 | h1544
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1545 | h1545
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1546 | h1546
                      · linarith only [h0, h1538, h1546, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1548 | h1548
                        · linarith only [h0, h1, h1540, h1548, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1550 | h1550
                          · linarith only [h0, h1, h1550, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · linarith only [h0, h1, h1542, h1550, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1432, h1537, h1545, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1543, h1544, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1555 | h1555
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1556 | h1556
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1557 | h1557
                      · linarith only [h0, h1538, h1557, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1559 | h1559
                        · linarith only [h0, h1, h1540, h1559, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1561 | h1561
                          · linarith only [h0, h1, h1561, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · linarith only [h0, h1, h1542, h1561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1, h1537, h1543, h1556, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h1, h1555, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1566 | h1566
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1567 | h1567
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1568 | h1568
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1569 | h1569
                      · linarith only [h0, h1, h1569, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1571 | h1571
                        · linarith only [h0, h1, h1571, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1573 | h1573
                          · linarith only [h0, h1542, h1573, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1575 | h1575
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1576 | h1576
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1577 | h1577
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1578 | h1578
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1579 | h1579
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1580 | h1580
                                      · rcases h0bigk with h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c | h1581c
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h0, h1432, h1575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1581_1, u1elo2]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1, hlam, p1581_1]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1432, hlam, p1581_1]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1432, h1575, hc05, hlam, hphi, ht01, ht0b, ht5b, p1581_1, u1elo2]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h0, hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1538, hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1540, hlam, p1581_1]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1542, hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1, hc01, hlam, hphi, p1581_1, u1elo2]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          rcases p1581_3 (m.d 0 1) (by simp) with h1593 | h1593
                                          · linarith only [h1, h1593, hlam]
                                          · linarith only [h0, h1593, hlam]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1, h1432, h1537, h1573, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1581_1, u1elo2]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          rcases p1581_3 (m.d 0 1) (by simp) with h1598 | h1598
                                          · linarith only [h1, h1598, hlam]
                                          · linarith only [h1537, h1598, hlam]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1537, h1573, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1581_1, u0elo3]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          rcases p1581_3 (m.d 0 1) (by simp) with h1602 | h1602
                                          · linarith only [h1432, h1602, hlam]
                                          · linarith only [h0, h1602, hlam]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1566, hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          rcases p1581_3 (m.d 0 1) (by simp) with h1607 | h1607
                                          · linarith only [h1432, h1607, hlam]
                                          · linarith only [h1537, h1607, hlam]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1537, hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1581_1, u5elo0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1567, hlam, p1581_0]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [h1568, hlam, p1581_1]
                                        · obtain ⟨p1581_0, p1581_1, p1581_2, p1581_3⟩ := h1581c
                                          linarith only [hlam, p1581_0]
                                      · linarith only [h1, h1537, h1577, h1580, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · linarith only [h1432, h1569, h1575, h1579, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h1432, h1537, h1569, h1573, h1575, h1578, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h1432, h1537, h1573, h1577, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1432, h1537, h1573, h1575, h1576, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h1566, h1575, hlam]
                    · linarith only [h1432, h1537, h1568, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1566, h1567, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1623 | h1623
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1624 | h1624
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1625 | h1625
                      · linarith only [h0, h1, h1625, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1627 | h1627
                        · linarith only [h0, h1, h1627, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1629 | h1629
                          · linarith only [h0, h1542, h1629, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1631 | h1631
                            · linarith only [h1, h1537, h1566, h1629, h1631, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h1, h1537, h1629, h1631, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h1537, h1566, h1624, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h1, h1623, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h1537, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1637 | h1637
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1638 | h1638
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1639 | h1639
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1640 | h1640
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1641 | h1641
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1642 | h1642
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1643 | h1643
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1644 | h1644
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1645 | h1645
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1646 | h1646
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1647 | h1647
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1648 | h1648
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1649 | h1649
                            · linarith only [h0, h1637, h1649, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h0, h1637, h1643, h1649, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h0, h1648, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1641, h1647, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1640, h1646, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1655 | h1655
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1656 | h1656
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1657 | h1657
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1658 | h1658
                            · linarith only [h0, h1637, h1658, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h0, h1637, h1643, h1658, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h0, h1657, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1641, h1656, hlam]
                      · linarith only [h0, h1640, h1655, hlam]
                  · linarith only [h1643, h1644, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1667 | h1667
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1668 | h1668
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1669 | h1669
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1670 | h1670
                            · linarith only [h1637, h1643, h1665, h1670, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1672 | h1672
                              · linarith only [h0, h1638, h1670, h1672, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h1643, h1665, h1667, h1672, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h1669, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1641, h1668, hlam]
                      · linarith only [h0, h1640, h1667, hlam]
                    · linarith only [h1643, h1665, h1666, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1679 | h1679
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1680 | h1680
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1681 | h1681
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1682 | h1682
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1683 | h1683
                            · linarith only [h1637, h1643, h1683, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1685 | h1685
                              · linarith only [h0, h1637, h1665, h1685, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1687 | h1687
                                · linarith only [h0, h1638, h1687, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h0, h1638, h1679, h1683, h1687, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h0, h1682, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1641, h1681, hlam]
                      · linarith only [h0, h1640, h1680, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1693 | h1693
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1694 | h1694
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1695 | h1695
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1696 | h1696
                            · linarith only [h1637, h1643, h1696, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1698 | h1698
                              · linarith only [h0, h1637, h1698, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1700 | h1700
                                · linarith only [h0, h1638, h1679, h1700, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1702 | h1702
                                  · linarith only [h1637, h1643, h1693, h1702, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1704 | h1704
                                    · linarith only [h1637, h1665, h1693, h1704, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1706 | h1706
                                      · rcases h0bigk with h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h0, hlam, p1707_1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h0, h1637, h1693, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1707_1, u1elo1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p1707_1, u1elo1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h0, h1638, h1679, h1694, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1707_1, u1elo1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h0, hc01, hlam, hphi, p1707_1, u1elo1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          rcases p1707_3 (m.d 0 1) (by simp) with h1715 | h1715
                                          · linarith only [h0, h1715, hlam]
                                          · linarith only [h1637, h1715, hlam]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          rcases p1707_3 (m.d 0 1) (by simp) with h1718 | h1718
                                          · linarith only [h0, h1718, hlam]
                                          · linarith only [h1638, h1718, hlam]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          rcases p1707_3 (m.d 0 1) (by simp) with h1721 | h1721
                                          · linarith only [h0, h1721, hlam]
                                          · linarith only [h1639, h1721, hlam]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1637, hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1640, hlam, p1707_1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1643, hlam, p1707_1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1665, hlam, p1707_1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1638, hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1641, hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1637, h1679, h1693, h1706, hc23, hc34, hlam, hphi, p1707_1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1679, hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1639, hlam, p1707_0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1642, hlam, p1707_1]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [h1637, h1693, hc23, hlam, hphi, ht34, ht45, p1707_1, u5elo0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [hc04, hlam, hphi, ht45, p1707_1, u5elo0]
                                        · obtain ⟨p1707_0, p1707_1, p1707_2, p1707_3⟩ := h1707c
                                          linarith only [hlam, p1707_0]
                                      · linarith only [h1637, h1643, h1693, h1706, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h1695, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1641, h1694, hlam]
                      · linarith only [h0, h1637, h1640, h1693, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1637, h1642, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h1638, h1641, hlam]
          · linarith only [h0, h1637, h1640, hlam]
        · linarith only [h1637, h1639, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1747 | h1747
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1748 | h1748
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1749 | h1749
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1750 | h1750
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1751 | h1751
                · linarith only [h1637, h1638, h1751, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1753 | h1753
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1754 | h1754
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1755 | h1755
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1756 | h1756
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1757 | h1757
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1758 | h1758
                            · linarith only [h1637, h1751, h1758, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1760 | h1760
                              · linarith only [h1637, h1638, h1756, h1760, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h1637, h1638, h1753, h1756, h1760, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h1638, h1756, h1757, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1749, h1756, hlam]
                      · linarith only [h0, h1748, h1755, hlam]
                    · linarith only [h1637, h1638, h1754, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1767 | h1767
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1768 | h1768
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1769 | h1769
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1770 | h1770
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1771 | h1771
                            · linarith only [h1637, h1751, h1771, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1773 | h1773
                              · linarith only [h1637, h1638, h1769, h1773, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1775 | h1775
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1776 | h1776
                                  · linarith only [h1638, h1748, h1771, h1776, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1778 | h1778
                                    · linarith only [h1638, h1747, h1753, h1768, h1769, h1773, h1778, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1780 | h1780
                                      · rcases h0bigk with h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h0, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1638, h1769, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1781_1, u1elo1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1638, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1638, h1769, hc05, hlam, hphi, ht01, ht0b, ht5b, p1781_1, u1elo1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h0, hc01, hlam, hphi, p1781_1, u1elo1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          rcases p1781_3 (m.d 0 1) (by simp) with h1789 | h1789
                                          · linarith only [h0, h1789, hlam]
                                          · linarith only [h1637, h1789, hlam]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h0, h1638, h1747, h1768, h1773, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1781_1, u1elo1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          rcases p1781_3 (m.d 0 1) (by simp) with h1793 | h1793
                                          · linarith only [h0, h1793, hlam]
                                          · linarith only [h1747, h1793, hlam]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1637, hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1748, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1751, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1753, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1747, h1768, h1773, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1781_1, u0elo3]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1749, hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          rcases p1781_3 (m.d 0 1) (by simp) with h1803 | h1803
                                          · linarith only [h1638, h1803, hlam]
                                          · linarith only [h1637, h1803, hlam]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          rcases p1781_3 (m.d 0 1) (by simp) with h1807 | h1807
                                          · linarith only [h1638, h1807, hlam]
                                          · linarith only [h1747, h1807, hlam]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1747, hlam, p1781_0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1750, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1637, h1768, hc23, hlam, hphi, ht34, ht45, p1781_1, u5elo0]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [h1767, hlam, p1781_1]
                                        · obtain ⟨p1781_0, p1781_1, p1781_2, p1781_3⟩ := h1781c
                                          linarith only [hlam, p1781_0]
                                      · linarith only [h0, h1638, h1747, h1771, h1775, h1780, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                · linarith only [h1638, h1775, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1637, h1638, h1750, h1768, h1769, h1770, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h0, h1749, h1769, hlam]
                      · linarith only [h0, h1748, h1768, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1637, h1638, h1767, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h1637, h1750, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1822 | h1822
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1823 | h1823
                · linarith only [h0, h1637, h1749, h1823, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1825 | h1825
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1826 | h1826
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1827 | h1827
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1828 | h1828
                        · linarith only [h0, h1637, h1749, h1827, h1828, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1830 | h1830
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
                            · linarith only [h1637, h1823, h1831, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1833 | h1833
                              · linarith only [h0, h1637, h1828, h1833, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h1637, h1825, h1828, h1833, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h0, h1830, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1638, h1748, h1749, h1827, hc01, hlam, hphi, u1elo3]
                    · linarith only [h0, h1637, h1749, h1826, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1839 | h1839
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1841 | h1841
                        · linarith only [h0, h1637, h1749, h1840, h1841, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1843 | h1843
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1844 | h1844
                            · linarith only [h1637, h1823, h1844, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1846 | h1846
                              · linarith only [h0, h1637, h1841, h1846, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1848 | h1848
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1849 | h1849
                                  · linarith only [h0, h1638, h1748, h1841, h1844, h1849, hc01, hc24, hlam, hphi, ht12]
                                  · linarith only [h0, h1747, h1840, h1841, h1846, h1849, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h1747, h1840, h1841, h1846, h1848, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h1843, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h1748, h1840, hlam]
                    · linarith only [h1637, h1638, h1839, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h1637, h1822, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h1637, h1748, hlam]
        · linarith only [h1637, h1747, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1859 | h1859
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1860 | h1860
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1861 | h1861
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1862 | h1862
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1863 | h1863
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1864 | h1864
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1865 | h1865
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1866 | h1866
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1867 | h1867
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1868 | h1868
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1869 | h1869
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1870 | h1870
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1871 | h1871
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1872 | h1872
                                · linarith only [h1637, h1859, h1867, h1872, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h1637, h1859, h1866, h1867, h1872, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · linarith only [h1637, h1871, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1637, h1861, h1864, h1870, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h1861, h1869, hc23, hlam, hphi, ht34, ht45, u5elo2]
                        · linarith only [h1637, h1859, h1862, h1867, h1868, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1861, h1867, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1880 | h1880
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1881 | h1881
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1882 | h1882
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1883 | h1883
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1884 | h1884
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1885 | h1885
                                · linarith only [h1637, h1859, h1885, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1887 | h1887
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1888 | h1888
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1889 | h1889
                                      · linarith only [h1859, h1866, h1881, h1887, h1889, hlam]
                                      · rcases h0bigk with h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h0, hlam, p1891_1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1637, hlam, p1891_1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1637, h1880, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p1891_1, u1elo1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1637, h1859, h1866, h1880, h1881, h1887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1891_1, u1elo1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h0, hc01, hlam, hphi, p1891_1, u1elo1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h0, h1637, h1859, h1881, h1887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1891_1, u1elo1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          rcases p1891_3 (m.d 0 1) (by simp) with h1900 | h1900
                                          · linarith only [h0, h1900, hlam]
                                          · linarith only [h1859, h1900, hlam]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          rcases p1891_3 (m.d 0 1) (by simp) with h1903 | h1903
                                          · linarith only [h0, h1903, hlam]
                                          · linarith only [h1860, h1903, hlam]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1860, h1882, h1888, h1889, hc34, hlam, hphi, ht0b, ht45, ht5b, p1891_1, u0elo2]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1861, hlam, p1891_1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          rcases p1891_3 (m.d 0 1) (by simp) with h1909 | h1909
                                          · linarith only [h1637, h1909, hlam]
                                          · linarith only [h1859, h1909, hlam]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          rcases p1891_3 (m.d 0 1) (by simp) with h1912 | h1912
                                          · linarith only [h1637, h1912, hlam]
                                          · linarith only [h1860, h1912, hlam]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1859, hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1862, hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1864, hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1866, hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1860, hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1863, hlam, p1891_1]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1865, hlam, p1891_0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [h1859, h1881, h1887, hc34, hlam, hphi, ht45, p1891_1, u5elo0]
                                        · obtain ⟨p1891_0, p1891_1, p1891_2, p1891_3⟩ := h1891c
                                          linarith only [hlam, p1891_0]
                                    · linarith only [h1637, h1860, h1880, h1884, h1888, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · linarith only [h1864, h1866, h1887, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h1637, h1884, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1637, h1864, h1883, hlam]
                          · linarith only [h1637, h1859, h1880, h1881, h1882, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1862, h1881, hlam]
                      · linarith only [h0, h1861, h1880, hlam]
                  · linarith only [h1637, h1859, h1865, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h1637, h1859, h1864, hlam]
              · linarith only [h0, h1859, h1863, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h1637, h1859, h1861, h1862, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1936 | h1936
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1937 | h1937
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1939 | h1939
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1940 | h1940
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1941 | h1941
                      · linarith only [h0, h1859, h1861, h1941, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1943 | h1943
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1944 | h1944
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1945 | h1945
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1946 | h1946
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1947 | h1947
                                · linarith only [h0, h1859, h1947, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h0, h1859, h1940, h1941, h1947, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · linarith only [h0, h1941, h1946, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h1938, h1941, h1945, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1859, h1943, h1944, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h1936, h1943, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1954 | h1954
                      · linarith only [h0, h1859, h1861, h1954, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1956 | h1956
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1957 | h1957
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1958 | h1958
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1959 | h1959
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1960 | h1960
                                · linarith only [h0, h1859, h1954, h1960, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1962 | h1962
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1963 | h1963
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1964 | h1964
                                      · linarith only [h0, h1860, h1940, h1954, h1956, h1960, h1962, h1964, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                      · rcases h0bigk with h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h0, hlam, p1966_1]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1637, hlam, p1966_1]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h0, h1954, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1966_1]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h0, h1954, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1966_1]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1860, hc15, hlam, hphi, ht0b, ht5b, p1966_1, u0elo1]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1861, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          rcases p1966_3 (m.d 0 1) (by simp) with h1975 | h1975
                                          · linarith only [h0, h1975, hlam]
                                          · linarith only [h1859, h1975, hlam]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          rcases p1966_3 (m.d 0 1) (by simp) with h1978 | h1978
                                          · linarith only [h0, h1978, hlam]
                                          · linarith only [h1860, h1978, hlam]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1637, hc01, hlam, hphi, p1966_1, u1elo2]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h0, h1637, h1860, h1956, h1960, h1962, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1966_1, u1elo2]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          rcases p1966_3 (m.d 0 1) (by simp) with h1984 | h1984
                                          · linarith only [h1637, h1984, hlam]
                                          · linarith only [h1859, h1984, hlam]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          rcases p1966_3 (m.d 0 1) (by simp) with h1987 | h1987
                                          · linarith only [h1637, h1987, hlam]
                                          · linarith only [h1860, h1987, hlam]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1859, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1936, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1938, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1940, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1860, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1937, hlam, p1966_1]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1939, hlam, p1966_0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [h1859, h1956, h1962, hc34, hlam, hphi, ht45, p1966_1, u5elo0]
                                        · obtain ⟨p1966_0, p1966_1, p1966_2, p1966_3⟩ := h1966c
                                          linarith only [hlam, p1966_0]
                                    · linarith only [h0, h1860, h1954, h1956, h1960, h1962, h1963, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · linarith only [h0, h1860, h1954, h1956, h1960, h1962, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h1637, h1959, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1637, h1938, h1958, hlam]
                          · linarith only [h0, h1957, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1859, h1936, h1956, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1859, h1861, h1939, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h1859, h1861, h1938, hlam]
              · linarith only [h0, h1859, h1937, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h1859, h1936, hlam]
        · linarith only [h1859, h1860, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2011 | h2011
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2012 | h2012
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2013 | h2013
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2014 | h2014
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2015 | h2015
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2016 | h2016
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2017 | h2017
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2018 | h2018
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2019 | h2019
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2020 | h2020
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2021 | h2021
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2022 | h2022
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2023 | h2023
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2024 | h2024
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2025 | h2025
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2026 | h2026
                                      · linarith only [h2012, h2024, h2026, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h0, h2011, h2023, h2026, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                    · linarith only [h1859, h2011, h2018, h2021, h2022, h2025, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2030 | h2030
                                    · linarith only [h1637, h2015, h2018, h2024, h2030, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                    · linarith only [h1859, h2011, h2018, h2021, h2022, h2030, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · linarith only [h1859, h2023, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1859, h2011, h2020, h2021, h2022, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1637, h2015, h2021, hlam]
                          · linarith only [h1637, h2015, h2018, h2020, hc34, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h2013, h2019, hlam]
                      · linarith only [h0, h2012, h2018, hlam]
                    · linarith only [h1859, h2011, h2017, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1859, h2011, h2015, h2016, hc15, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2041 | h2041
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2042 | h2042
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2043 | h2043
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2044 | h2044
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2045 | h2045
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2046 | h2046
                            · linarith only [h2015, h2041, h2043, h2046, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2048 | h2048
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2049 | h2049
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2050 | h2050
                                  · linarith only [h2012, h2046, h2050, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2052 | h2052
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2053 | h2053
                                      · rcases h0bigk with h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c | h2054c
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h0, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h1637, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h1859, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h1637, h2046, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h0, hc01, hlam, hphi, p2054_1, u1elo1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h0, h1637, h2011, h2045, h2052, h2053, hc45, hlam, hphi, ht01, ht0b, ht5b, p2054_1, u1elo1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h0, h1637, h2011, h2015, h2045, h2052, h2053, hc45, hlam, hphi, ht01, ht0b, ht5b, p2054_1, u1elo1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          rcases p2054_3 (m.d 0 1) (by simp) with h2064 | h2064
                                          · linarith only [h0, h2064, hlam]
                                          · linarith only [h2011, h2064, hlam]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2011, h2045, h2052, h2053, hc45, hlam, hphi, ht0b, ht5b, p2054_1, u0elo2]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2012, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2015, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          rcases p2054_3 (m.d 0 1) (by simp) with h2071 | h2071
                                          · linarith only [h1637, h2071, hlam]
                                          · linarith only [h2011, h2071, hlam]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h0, h2011, h2013, h2045, h2052, h2053, hc45, hlam, hphi, ht01, ht0b, ht5b, p2054_1, u1elo1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2013, hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h0, h1637, h2011, h2013, h2045, h2052, h2053, hc45, hlam, hphi, ht01, ht0b, ht5b, p2054_1, u1elo1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          rcases p2054_3 (m.d 0 1) (by simp) with h2078 | h2078
                                          · linarith only [h1859, h2078, hlam]
                                          · linarith only [h2011, h2078, hlam]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2011, hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2014, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2041, hlam, p2054_0]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [h2042, hlam, p2054_1]
                                        · obtain ⟨p2054_0, p2054_1, p2054_2, p2054_3⟩ := h2054c
                                          linarith only [hlam, p2054_0]
                                      · linarith only [h1637, h2046, h2053, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                    · linarith only [h1637, h2041, h2046, h2052, hc23, hc34, hlam, hphi]
                                · linarith only [h1859, h2011, h2045, h2049, hc25, hlam, hphi, u5elo4]
                              · linarith only [h1637, h2011, h2045, h2048, hc25, hlam, hphi, u5elo3]
                          · linarith only [h0, h2013, h2045, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h1637, h2011, h2013, h2043, h2044, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h2012, h2043, hlam]
                    · linarith only [h1637, h2011, h2015, h2042, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1637, h2011, h2041, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h2011, h2014, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2096 | h2096
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2097 | h2097
                · linarith only [h2012, h2013, h2097, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2099 | h2099
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2100 | h2100
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2101 | h2101
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2102 | h2102
                        · linarith only [h2012, h2013, h2102, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2104 | h2104
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2105 | h2105
                            · linarith only [h1637, h2011, h2097, h2104, h2105, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2107 | h2107
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2108 | h2108
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2109 | h2109
                                  · linarith only [h2012, h2105, h2109, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2111 | h2111
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2112 | h2112
                                      · rcases h0bigk with h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c | h2113c
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [hlam, p2113_0]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h0, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h1637, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h1859, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h1637, hc05, hlam, hphi, ht01, ht0b, ht5b, p2113_1, u1elo2]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h0, h2102, h2109, hc01, hc34, hlam, hphi, ht12, ht23, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [hlam, p2113_0]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h0, h2102, h2109, hc03, hc34, hlam, hphi, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2013, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          rcases p2113_3 (m.d 0 1) (by simp) with h2123 | h2123
                                          · linarith only [h0, h2123, hlam]
                                          · linarith only [h2011, h2123, hlam]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2011, h2104, h2111, h2112, hc45, hlam, hphi, ht0b, ht5b, p2113_1, u0elo2]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2012, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [hlam, p2113_0]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2097, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          rcases p2113_3 (m.d 0 1) (by simp) with h2130 | h2130
                                          · linarith only [h1637, h2130, hlam]
                                          · linarith only [h2011, h2130, hlam]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2011, h2104, h2111, h2112, hc45, hlam, hphi, ht0b, ht5b, p2113_1, u0elo3]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h1859, h2012, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2113_1, u1elo3]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h1637, h1859, h2011, h2104, h2111, h2112, hc45, hlam, hphi, ht01, ht0b, ht5b, p2113_1, u1elo3]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [hlam, p2113_0]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          rcases p2113_3 (m.d 0 1) (by simp) with h2137 | h2137
                                          · linarith only [h1859, h2137, hlam]
                                          · linarith only [h2011, h2137, hlam]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2011, hlam, p2113_0]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2096, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2099, hlam, p2113_0]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [h2100, hlam, p2113_1]
                                        · obtain ⟨p2113_0, p2113_1, p2113_2, p2113_3⟩ := h2113c
                                          linarith only [hlam, p2113_0]
                                      · linarith only [h1637, h2011, h2101, h2102, h2104, h2109, h2111, h2112, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h1637, h2099, h2101, h2102, h2109, h2111, hc23, hc34, hlam, hphi]
                                · linarith only [h1859, h2011, h2104, h2108, hc25, hlam, hphi, u5elo4]
                              · linarith only [h1637, h2011, h2104, h2107, hc25, hlam, hphi, u5elo3]
                          · linarith only [h1637, h2011, h2101, h2104, hc15, hlam, hphi, u5elo2]
                      · linarith only [h0, h2012, h2101, hlam]
                    · linarith only [h1859, h2011, h2100, hc15, hlam, hphi, u5elo4]
                  · linarith only [h1637, h2011, h2099, hc15, hlam, hphi, u5elo3]
              · linarith only [h2012, h2096, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2154 | h2154
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2155 | h2155
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2156 | h2156
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2157 | h2157
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2158 | h2158
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2159 | h2159
                      · linarith only [h2012, h2154, h2159, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2161 | h2161
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2162 | h2162
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2163 | h2163
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2164 | h2164
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2165 | h2165
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2166 | h2166
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2167 | h2167
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2168 | h2168
                                      · rcases h0bigk with h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c | h2169c
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h0, hlam, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h1637, hlam, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h1859, hlam, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h0, h2159, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h0, h2159, hc01, hc23, hlam, hphi, ht12, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2012, hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h0, h1859, h2011, h2159, h2162, h2167, h2168, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          rcases p2169_3 (m.d 0 1) (by simp) with h2179 | h2179
                                          · linarith only [h0, h2179, hlam]
                                          · linarith only [h2011, h2179, hlam]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2011, h2162, h2167, h2168, hc45, hlam, hphi, ht0b, ht5b, p2169_1, u0elo2]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h0, h1637, h2011, h2162, h2167, h2168, hc45, hlam, hphi, ht01, ht0b, ht5b, p2169_1, u1elo2]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h1637, h1859, h2011, h2162, h2167, h2168, hc45, hlam, hphi, ht01, ht0b, ht5b, p2169_1, u1elo2]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          rcases p2169_3 (m.d 0 1) (by simp) with h2186 | h2186
                                          · linarith only [h1637, h2186, hlam]
                                          · linarith only [h2011, h2186, hlam]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2011, h2162, h2167, h2168, hc45, hlam, hphi, ht0b, ht5b, p2169_1, u0elo3]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2154, hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2156, hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          rcases p2169_3 (m.d 0 1) (by simp) with h2193 | h2193
                                          · linarith only [h1859, h2193, hlam]
                                          · linarith only [h2011, h2193, hlam]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2011, hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2155, hlam, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2157, hlam, p2169_0]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [h2158, hlam, p2169_1]
                                        · obtain ⟨p2169_0, p2169_1, p2169_2, p2169_3⟩ := h2169c
                                          linarith only [hlam, p2169_0]
                                      · linarith only [h1859, h2011, h2159, h2161, h2165, h2168, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1859, h2159, h2161, h2167, hc01, hc35, hlam, hphi, ht12, ht23]
                                  · linarith only [h1859, h2011, h2159, h2161, h2165, h2166, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1859, h2165, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1637, h2156, h2164, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h1637, h2156, h2163, hlam]
                          · linarith only [h1859, h2011, h2161, h2162, hc15, hlam, hphi, u5elo2]
                        · linarith only [h0, h2154, h2161, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1859, h2011, h2158, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h2011, h2012, h2157, hc15, hlam, hphi, u5elo3]
                · linarith only [h2012, h2154, h2156, hlam]
              · linarith only [h1859, h2011, h2154, h2155, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2213 | h2213
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2214 | h2214
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2215 | h2215
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2216 | h2216
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2217 | h2217
                      · linarith only [h2012, h2213, h2217, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2219 | h2219
                        · linarith only [h0, h2011, h2154, h2217, h2219, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2221 | h2221
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2222 | h2222
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2223 | h2223
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2224 | h2224
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2225 | h2225
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2226 | h2226
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2227 | h2227
                                      · rcases h0bigk with h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c | h2228c
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h0, hlam, p2228_1]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h1637, hlam, p2228_1]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h1859, hlam, p2228_1]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h0, h2219, h2222, hc05, hlam, hphi, ht01, ht0b, ht5b, p2228_1, u1elo2]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h0, h2219, h2222, hc01, hlam, hphi, p2228_1, u1elo2]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2012, hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2154, hlam, p2228_1]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          rcases p2228_3 (m.d 0 1) (by simp) with h2238 | h2238
                                          · linarith only [h0, h2238, hlam]
                                          · linarith only [h2011, h2238, hlam]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2011, h2221, h2226, h2227, hc45, hlam, hphi, ht0b, ht5b, p2228_1, u0elo2]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h0, h1637, h2011, h2221, h2226, h2227, hc45, hlam, hphi, ht01, ht0b, ht5b, p2228_1, u1elo2]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h0, h1637, h2011, h2154, h2221, h2226, h2227, hc45, hlam, hphi, ht01, ht0b, ht5b, p2228_1, u1elo2]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          rcases p2228_3 (m.d 0 1) (by simp) with h2245 | h2245
                                          · linarith only [h1637, h2245, hlam]
                                          · linarith only [h2011, h2245, hlam]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2011, h2221, h2226, h2227, hc45, hlam, hphi, ht0b, ht5b, p2228_1, u0elo3]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h0, h1859, h2011, h2221, h2222, h2226, h2227, hc45, hlam, hphi, ht01, ht0b, ht5b, p2228_1, u1elo2]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2214, hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          rcases p2228_3 (m.d 0 1) (by simp) with h2252 | h2252
                                          · linarith only [h1859, h2252, hlam]
                                          · linarith only [h2011, h2252, hlam]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2011, hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2213, hlam, p2228_1]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2215, hlam, p2228_0]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [h2216, hlam, p2228_1]
                                        · obtain ⟨p2228_0, p2228_1, p2228_2, p2228_3⟩ := h2228c
                                          linarith only [hlam, p2228_0]
                                      · linarith only [h0, h2011, h2219, h2222, h2224, h2227, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                    · linarith only [h0, h2012, h2226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h0, h2011, h2217, h2221, h2225, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h2011, h2219, h2221, h2224, hc25, hlam, hphi, u5elo4]
                              · linarith only [h0, h2011, h2219, h2221, h2222, h2223, hc25, hlam, hphi, u5elo3]
                            · linarith only [h1637, h2214, h2222, hlam]
                          · linarith only [h0, h2221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h1859, h2011, h2216, hc15, hlam, hphi, u5elo4]
                  · linarith only [h2214, h2215, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2269 | h2269
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2270 | h2270
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2271 | h2271
                      · linarith only [h0, h2011, h2012, h2271, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2273 | h2273
                        · linarith only [h0, h2011, h2154, h2273, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2275 | h2275
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2276 | h2276
                            · linarith only [h0, h2011, h2012, h2214, h2275, h2276, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2278 | h2278
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2279 | h2279
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2280 | h2280
                                  · linarith only [h0, h2011, h2271, h2275, h2276, h2280, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h2011, h2271, h2275, h2280, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h2011, h2271, h2275, h2276, h2279, hc25, hlam, hphi, u5elo4]
                              · linarith only [h0, h2011, h2271, h2275, h2278, hc25, hlam, hphi, u5elo3]
                          · linarith only [h0, h2011, h2275, hc15, hlam, hphi, u5elo2]
                    · linarith only [h0, h2011, h2012, h2214, h2270, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h2011, h2012, h2269, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h2011, h2213, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2289 | h2289
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2290 | h2290
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2291 | h2291
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2292 | h2292
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2293 | h2293
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2294 | h2294
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2295 | h2295
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2296 | h2296
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2297 | h2297
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2298 | h2298
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2299 | h2299
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2300 | h2300
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2301 | h2301
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2302 | h2302
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2303 | h2303
                                      · linarith only [h2289, h2301, h2303, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · rcases h0bigk with h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c | h2305c
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h0, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1637, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1859, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2011, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h0, hc01, hlam, hphi, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h0, h2292, h2294, h2303, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h0, h2294, h2303, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h0, h2294, h2303, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1637, h2295, hc01, hlam, hphi, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2289, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1637, h2294, h2295, h2303, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1637, h2294, h2295, h2303, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1859, h2295, h2298, hc01, hlam, hphi, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2290, hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2292, hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h1859, h2294, h2295, h2298, h2303, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2305_1, u1elo1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2305_1, u5elo0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2291, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2293, hlam, p2305_0]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [h2294, hlam, p2305_1]
                                        · obtain ⟨p2305_0, p2305_1, p2305_2, p2305_3⟩ := h2305c
                                          linarith only [hlam, p2305_0]
                                    · linarith only [h1637, h2293, h2295, h2301, h2302, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2332 | h2332
                                    · linarith only [h1637, h2292, h2295, h2301, h2332, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2334 | h2334
                                      · rcases h0bigk with h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h0, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1637, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1859, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2011, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h0, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h0, h2292, h2332, h2334, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h0, h1859, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h0, h2011, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1637, h2295, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2289, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1637, h1859, h2295, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1637, h2011, h2295, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1859, h2295, h2298, hc01, hlam, hphi, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2290, hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2292, hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h1859, h2293, h2295, h2298, h2332, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2335_1, u1elo1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2335_1, u5elo0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2291, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2293, hlam, p2335_0]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [h2294, hlam, p2335_1]
                                        · obtain ⟨p2335_0, p2335_1, p2335_2, p2335_3⟩ := h2335c
                                          linarith only [hlam, p2335_0]
                                      · linarith only [h1859, h2294, h2295, h2298, h2301, h2334, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · linarith only [h1859, h2294, h2300, hlam]
                              · linarith only [h1859, h2294, h2298, h2299, hc45, hlam, hphi, u5elo3]
                            · linarith only [h1637, h2292, h2298, hlam]
                          · linarith only [h0, h2289, h2292, h2297, hc34, hlam, hphi, ht45, u5elo2]
                        · linarith only [h1637, h2290, h2295, h2296, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h2289, h2295, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2368 | h2368
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2369 | h2369
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2370 | h2370
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2371 | h2371
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2372 | h2372
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2373 | h2373
                                · linarith only [h1859, h2294, h2373, hc01, hlam, hphi, u1elo3]
                                · linarith only [h1859, h2373, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1637, h2293, h2372, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                            · linarith only [h1637, h2289, h2292, h2371, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h2291, h2370, hlam]
                        · linarith only [h0, h1859, h2290, h2369, hc01, hlam, hphi, u1elo3]
                      · linarith only [h0, h2289, h2368, hlam]
                  · linarith only [h2292, h2293, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2382 | h2382
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2383 | h2383
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2384 | h2384
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2385 | h2385
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2386 | h2386
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2387 | h2387
                            · linarith only [h2292, h2382, h2384, h2387, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2389 | h2389
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2390 | h2390
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2391 | h2391
                                  · linarith only [h1637, h2289, h2387, h2391, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2393 | h2393
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2394 | h2394
                                      · rcases h0bigk with h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [hlam, p2395_0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h0, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1637, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1859, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2011, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h0, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [hlam, p2395_0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h0, h1637, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h0, h1859, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h0, h2011, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1637, h2387, hc01, hc34, hlam, hphi, ht12, ht23, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2289, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [hlam, p2395_0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2292, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1637, h2011, h2387, hc01, hc34, hlam, hphi, ht12, ht23, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1859, h2385, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2290, hlam, p2395_0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1637, h1859, h2385, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [hlam, p2395_0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h1859, h2011, h2385, hc01, hlam, hphi, p2395_1, u1elo1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2395_1, u5elo0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2291, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2382, hlam, p2395_0]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [h2383, hlam, p2395_1]
                                        · obtain ⟨p2395_0, p2395_1, p2395_2, p2395_3⟩ := h2395c
                                          linarith only [hlam, p2395_0]
                                      · linarith only [h2387, h2394, hc13, hlam, hphi, ht34, ht45, u5elo4]
                                    · linarith only [h1637, h2382, h2387, h2393, hc23, hc34, hlam, hphi]
                                · linarith only [h1859, h2383, h2390, hlam]
                              · linarith only [h1637, h2382, h2389, hlam]
                          · linarith only [h0, h2290, h2386, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h2290, h2385, hlam]
                      · linarith only [h0, h2289, h2384, hlam]
                    · linarith only [h2292, h2382, h2383, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2429 | h2429
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2430 | h2430
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2431 | h2431
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2432 | h2432
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2433 | h2433
                            · linarith only [h1637, h2292, h2433, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2435 | h2435
                              · linarith only [h1637, h2382, h2431, h2433, h2435, hc01, hlam, hphi, u1elo1]
                              · linarith only [h1637, h2435, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h2291, h2432, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1859, h2290, h2431, hc01, hlam, hphi, u1elo3]
                      · linarith only [h0, h2289, h2430, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2441 | h2441
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2442 | h2442
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2443 | h2443
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2444 | h2444
                            · linarith only [h1637, h2292, h2444, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2446 | h2446
                              · linarith only [h1637, h2382, h2444, h2446, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1637, h2446, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h2291, h2443, hlam]
                        · linarith only [h0, h1859, h2290, h2442, hc01, hlam, hphi, u1elo3]
                      · linarith only [h0, h2289, h2292, h2429, h2441, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h2289, h2291, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2453 | h2453
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2454 | h2454
                · linarith only [h2289, h2290, h2454, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2456 | h2456
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2457 | h2457
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2458 | h2458
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2459 | h2459
                        · linarith only [h2289, h2290, h2459, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2461 | h2461
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2462 | h2462
                            · linarith only [h2454, h2456, h2462, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2464 | h2464
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2465 | h2465
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2466 | h2466
                                  · linarith only [h2289, h2462, h2466, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2468 | h2468
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2469 | h2469
                                      · rcases h0bigk with h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c | h2470c
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [hlam, p2470_0]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h0, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h1637, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h1859, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2011, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h0, h2459, h2466, hc01, hc34, hlam, hphi, ht12, ht23, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [hlam, p2470_0]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h0, h2289, h2459, h2466, h2468, h2469, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2290, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h0, h2011, h2459, h2466, hc01, hc34, hlam, hphi, ht12, ht23, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h1637, hc01, hlam, hphi, p2470_1, u1elo2]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2289, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [hlam, p2470_0]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2454, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h0, h2011, h2289, h2459, h2466, hc01, hc34, hlam, hphi, ht12, ht23, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h1859, hc01, hlam, hphi, p2470_1, u1elo3]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h0, h1859, hc01, hlam, hphi, p2470_1, u1elo3]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h1859, h2289, h2468, h2469, hc45, hlam, hphi, ht01, ht0b, ht5b, p2470_1, u1elo3]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [hlam, p2470_0]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h1859, h2011, hc01, hlam, hphi, p2470_1, u1elo3]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2470_1, u5elo0]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2453, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2456, hlam, p2470_0]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [h2457, hlam, p2470_1]
                                        · obtain ⟨p2470_0, p2470_1, p2470_2, p2470_3⟩ := h2470c
                                          linarith only [hlam, p2470_0]
                                      · linarith only [h0, h2289, h2459, h2466, h2468, h2469, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                    · linarith only [h1637, h2456, h2458, h2459, h2466, h2468, hc23, hc34, hlam, hphi]
                                · linarith only [h1859, h2457, h2465, hlam]
                              · linarith only [h1637, h2456, h2464, hlam]
                          · linarith only [h1637, h2456, h2458, h2461, hc35, hlam, hphi, u5elo2]
                      · linarith only [h0, h2289, h2458, hlam]
                    · linarith only [h2289, h2290, h2457, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2503 | h2503
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2504 | h2504
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2505 | h2505
                        · linarith only [h2289, h2290, h2505, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2507 | h2507
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2508 | h2508
                            · linarith only [h1637, h2454, h2508, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2510 | h2510
                              · linarith only [h1637, h2456, h2508, h2510, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1637, h2510, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h2453, h2507, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1859, h2289, h2290, h2504, hc01, hlam, hphi, u1elo3]
                    · linarith only [h2289, h2290, h2503, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h2289, h2453, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h2517 | h2517
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2518 | h2518
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2519 | h2519
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2520 | h2520
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2521 | h2521
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2522 | h2522
                      · linarith only [h2289, h2517, h2522, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2524 | h2524
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2525 | h2525
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2526 | h2526
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2527 | h2527
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2528 | h2528
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2529 | h2529
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2530 | h2530
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2531 | h2531
                                      · rcases h0bigk with h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h0, hlam, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1637, hlam, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1859, hlam, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2011, hlam, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h0, hc01, hlam, hphi, p2532_1, u1elo1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2289, hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h0, h1859, h2522, hc01, hlam, hphi, p2532_1, u1elo2]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h0, h2011, h2522, hc01, hlam, hphi, p2532_1, u1elo2]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1637, hc01, hlam, hphi, p2532_1, u1elo2]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1637, h2517, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2532_1, u1elo2]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1637, h2517, h2529, h2531, hc45, hlam, hphi, ht01, ht0b, ht5b, p2532_1, u1elo2]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1637, h2011, hc01, hlam, hphi, p2532_1, u1elo2]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h1859, hc01, hlam, hphi, p2532_1, u1elo3]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2517, hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2519, hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h0, h2011, h2517, h2522, hc01, hc23, hlam, hphi, ht12, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2532_1, u5elo0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2518, hlam, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2520, hlam, p2532_0]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [h2521, hlam, p2532_1]
                                        · obtain ⟨p2532_0, p2532_1, p2532_2, p2532_3⟩ := h2532c
                                          linarith only [hlam, p2532_0]
                                      · rcases h0bigk with h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c | h2558c
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h0, hlam, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h1637, hlam, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h1859, hlam, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2011, hlam, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h0, h2522, hc01, hc23, hlam, hphi, ht12, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2289, hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h0, h2521, h2522, h2531, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h0, h2011, h2522, hc01, hc23, hlam, hphi, ht12, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h1637, hc01, hlam, hphi, p2558_1, u1elo2]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h1637, h2518, hc25, hlam, hphi, ht01, ht0b, ht5b, p2558_1, u1elo2]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h1637, h2521, h2531, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2558_1, u1elo2]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h1637, h2011, hc01, hlam, hphi, p2558_1, u1elo2]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h0, h2517, h2522, hc01, hc23, hlam, hphi, ht12, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2517, hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2519, hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h0, h2011, h2517, h2522, hc01, hc23, hlam, hphi, ht12, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2558_1, u5elo0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2518, hlam, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2520, hlam, p2558_0]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [h2521, hlam, p2558_1]
                                        · obtain ⟨p2558_0, p2558_1, p2558_2, p2558_3⟩ := h2558c
                                          linarith only [hlam, p2558_0]
                                    · linarith only [h0, h1637, h2520, h2522, h2530, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                                  · linarith only [h2011, h2522, h2524, h2528, h2529, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1859, h2517, h2521, h2528, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h1637, h2520, h2527, hlam]
                            · linarith only [h1637, h2519, h2526, hlam]
                          · linarith only [h0, h2517, h2525, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h0, h2517, h2524, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2591 | h2591
                      · linarith only [h2289, h2518, h2591, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2593 | h2593
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2594 | h2594
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2595 | h2595
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2596 | h2596
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2597 | h2597
                                · linarith only [h1859, h2521, h2597, hc01, hlam, hphi, u1elo3]
                                · linarith only [h1859, h2597, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1637, h2520, h2596, hlam]
                            · linarith only [h1637, h1859, h2519, h2595, hc01, hlam, hphi, u1elo3]
                          · linarith only [h0, h2594, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h2517, h2593, hlam]
                  · linarith only [h2289, h2517, h2520, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h2289, h2517, h2519, hlam]
              · linarith only [h2517, h2518, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h2607 | h2607
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2608 | h2608
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2609 | h2609
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2610 | h2610
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2611 | h2611
                      · linarith only [h2289, h2607, h2611, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2613 | h2613
                        · linarith only [h2517, h2607, h2613, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2615 | h2615
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2616 | h2616
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2617 | h2617
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2618 | h2618
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2619 | h2619
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2620 | h2620
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2621 | h2621
                                      · rcases h0bigk with h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c | h2622c
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h0, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1637, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1859, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2011, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h0, h2613, h2616, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2289, hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2517, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h0, h2011, h2613, h2616, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1637, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h0, h1637, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1637, h1859, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1637, h2011, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1859, h2616, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1859, h2607, h2616, h2620, h2621, hc45, hlam, hphi, ht01, ht0b, ht5b, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2608, hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h1859, h2011, h2616, hc01, hlam, hphi, p2622_1, u1elo2]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2622_1, u5elo0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2607, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2609, hlam, p2622_0]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [h2610, hlam, p2622_1]
                                        · obtain ⟨p2622_0, p2622_1, p2622_2, p2622_3⟩ := h2622c
                                          linarith only [hlam, p2622_0]
                                      · rcases h0bigk with h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c | h2648c
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h0, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1637, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1859, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2011, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h0, h2613, h2616, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2289, hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2517, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h0, h2011, h2613, h2616, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1637, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h0, h1637, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1637, h2610, hc45, hlam, hphi, ht01, ht0b, ht5b, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1637, h2011, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1859, h2616, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1859, h2607, h2616, h2620, h2621, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2608, hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h1859, h2011, h2616, hc01, hlam, hphi, p2648_1, u1elo2]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2648_1, u5elo0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2607, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2609, hlam, p2648_0]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [h2610, hlam, p2648_1]
                                        · obtain ⟨p2648_0, p2648_1, p2648_2, p2648_3⟩ := h2648c
                                          linarith only [hlam, p2648_0]
                                    · linarith only [h2289, h2620, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                                  · linarith only [h0, h2611, h2619, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1859, h2618, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1637, h2608, h2609, h2617, hc34, hlam, hphi, ht45, u5elo0]
                            · linarith only [h1637, h2608, h2616, hlam]
                          · linarith only [h0, h2615, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2517, h2607, h2610, hc25, hlam, hphi, u5elo4]
                  · linarith only [h2517, h2607, h2608, h2609, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2682 | h2682
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2683 | h2683
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2684 | h2684
                      · linarith only [h2289, h2607, h2684, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2686 | h2686
                        · linarith only [h2517, h2607, h2684, h2686, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2688 | h2688
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h2689 | h2689
                            · linarith only [h2608, h2682, h2689, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h2691 | h2691
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h2692 | h2692
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h2693 | h2693
                                  · linarith only [h0, h2684, h2689, h2693, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h2011, h2684, h2688, h2693, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h2011, h2683, h2684, h2688, h2689, h2692, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h2011, h2684, h2688, h2691, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h2607, h2688, hlam]
                    · linarith only [h2517, h2607, h2683, hc25, hlam, hphi, u5elo4]
                  · linarith only [h2289, h2607, h2682, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h2701 | h2701
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2702 | h2702
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2703 | h2703
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2704 | h2704
                      · linarith only [h0, h2289, h2704, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2706 | h2706
                        · linarith only [h0, h2517, h2706, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2708 | h2708
                          · linarith only [h0, h2607, h2704, h2708, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h2708, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2711 | h2711
                      · linarith only [h0, h2289, h2711, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2713 | h2713
                        · linarith only [h0, h2517, h2711, h2713, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2715 | h2715
                          · linarith only [h0, h2607, h2711, h2715, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2715, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h2701, h2702, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h2719 | h2719
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2720 | h2720
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2721 | h2721
                      · linarith only [h0, h2289, h2721, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2723 | h2723
                        · linarith only [h0, h2517, h2721, h2723, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2725 | h2725
                          · linarith only [h0, h2607, h2721, h2725, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2725, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2701, h2719, h2720, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h2729 | h2729
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2730 | h2730
                      · linarith only [h0, h2289, h2730, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2732 | h2732
                        · linarith only [h0, h2517, h2732, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2734 | h2734
                          · linarith only [h0, h2607, h2730, h2734, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2734, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h2737 | h2737
                      · linarith only [h0, h2289, h2737, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h2739 | h2739
                        · linarith only [h0, h2517, h2739, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h2741 | h2741
                          · linarith only [h0, h2607, h2737, h2741, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2741, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem n7l_sAA5_M_LR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h10, h16, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                                  · linarith only [h0, h10, h19, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h13, h19, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h13, h14, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h13, h23, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                  · linarith only [h0, h13, h26, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                    · linarith only [h0, h10, h23, h28, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                                      · linarith only [h0, h11, h30, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                      · linarith only [h2, h25, h30, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                                  · linarith only [h0, h10, h13, h25, h33, h4, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                                    · linarith only [h0, h23, h35, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                                      · linarith only [h11, h25, h37, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                                        · linarith only [h0, h25, h39, h4, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                        · linarith only [h0, h10, h13, h39, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                        · linarith only [h0, h10, h4, h44, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h10, h4, h46, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                                        · linarith only [h1, h48, h54, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                        · linarith only [h2, h50, h54, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · linarith only [h44, h50, h53, hlam]
                                    · linarith only [h10, h49, h52, hlam]
                                  · linarith only [h0, h10, h4, h49, h51, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                      · linarith only [h0, h4, h50, h60, h62, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · linarith only [h0, h4, h44, h62, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                    · linarith only [h0, h10, h4, h61, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h10, h48, h60, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h0, h4, h48, h49, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h0, h4, h48, h68, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                                  · linarith only [h0, h4, h48, h71, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h4, h7, h71, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                                  · linarith only [h0, h10, h4, h48, h74, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h10, h4, h7, h74, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                                · linarith only [h82, h9, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                                  · linarith only [h0, h77, h84, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h80, h84, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h0, h4, h8, h80, h81, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                              · linarith only [h0, h4, h7, h80, h88, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h9, h90, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                                  · linarith only [h0, h4, h80, h92, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                                    · linarith only [h0, h77, h88, h90, h94, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                                      · linarith only [h9, h96, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                                        · linarith only [h0, h4, h7, h9, h98, hlam, hphi, ht01, u0ehi8, u1elo0]
                                        · rcases h1bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            rcases p100_3 (m.d 0 1) (by simp) with h103 | h103
                                            · rcases p100_3 (m.d 1 2) (by simp) with h104 | h104
                                              · linarith only [h0, h104, hlam]
                                              · linarith only [h104, h77, hlam]
                                            · linarith only [h103, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            rcases p100_3 (m.d 0 1) (by simp) with h108 | h108
                                            · rcases p100_3 (m.d 1 2) (by simp) with h109 | h109
                                              · linarith only [h0, h109, hlam]
                                              · linarith only [h109, h78, hlam]
                                            · linarith only [h108, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            rcases p100_3 (m.d 0 1) (by simp) with h113 | h113
                                            · rcases p100_3 (m.d 1 2) (by simp) with h114 | h114
                                              · linarith only [h0, h114, hlam]
                                              · linarith only [h114, h79, hlam]
                                            · linarith only [h113, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h0, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h0, h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h0, h77, h80, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h0, h77, h80, h90, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h1, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h77, hlam, p100_1]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h80, hlam, p100_1]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h88, hlam, p100_1]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h2, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h78, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h2, h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h90, hlam, p100_1]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h3, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h79, hlam, p100_0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h3, h77, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [h0, h4, h8, h88, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p100_1, u1elo0]
                                          · obtain ⟨p100_0, p100_1, p100_2, p100_3⟩ := h100c
                                            linarith only [hlam, p100_0]
                          · linarith only [h0, h6, h78, h79, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h0, h5, h77, h78, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                        · linarith only [h0, h140, h4, h77, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h0, h142, h4, h77, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                                · linarith only [h146, h9, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                                      · linarith only [h0, h148, h150, h4, h9, hlam, hphi, ht01, u0ehi8, u1elo0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h152 | h152
                                        · linarith only [h144, h152, h9, hlam, hphi, ht01, u0ehi8, u1elo2]
                                        · rcases h1bigk with h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            rcases p154_3 (m.d 0 1) (by simp) with h156 | h156
                                            · rcases p154_3 (m.d 1 2) (by simp) with h157 | h157
                                              · linarith only [h157, hlam, p154_0]
                                              · rcases p154_3 (m.d 1 3) (by simp) with h159 | h159
                                                · linarith only [h1, h159, hlam]
                                                · linarith only [h159, h77, hlam]
                                            · linarith only [h156, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h145, h152, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            rcases p154_3 (m.d 0 1) (by simp) with h164 | h164
                                            · rcases p154_3 (m.d 1 2) (by simp) with h165 | h165
                                              · linarith only [h0, h165, hlam]
                                              · rcases p154_3 (m.d 1 3) (by simp) with h167 | h167
                                                · linarith only [h1, h167, hlam]
                                                · linarith only [h144, h167, hlam]
                                            · linarith only [h164, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            rcases p154_3 (m.d 0 1) (by simp) with h171 | h171
                                            · rcases p154_3 (m.d 1 2) (by simp) with h172 | h172
                                              · linarith only [h0, h172, hlam]
                                              · rcases p154_3 (m.d 1 3) (by simp) with h174 | h174
                                                · linarith only [h1, h174, hlam]
                                                · linarith only [h145, h174, hlam]
                                            · linarith only [h171, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h0, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h77, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h140, hlam, p154_1]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h142, hlam, p154_1]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h1, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h0, h4, h77, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h0, h4, h77, hc15, hlam, hphi, ht01, ht0b, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h2, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h144, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h146, hlam, p154_1]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h3, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h145, hlam, p154_0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [h0, h142, h149, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p154_1, u1elo0]
                                          · obtain ⟨p154_0, p154_1, p154_2, p154_3⟩ := h154c
                                            linarith only [hlam, p154_0]
                                    · linarith only [h0, h149, h4, h77, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h145, h148, h4, h7, h77, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · linarith only [h0, h144, h145, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                              · linarith only [h0, h144, h201, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                                · linarith only [h203, h9, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                                  · linarith only [h0, h144, h205, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h0, h205, h4, h7, h77, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h208 | h208
                    · linarith only [h208, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h214 | h214
                              · linarith only [h210, h214, h8, hlam, hphi, ht01, u0ehi7, u1elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                                · linarith only [h0, h208, h212, h213, h214, h216, hlam, hphi, ht01, u0ehi8, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                                  · linarith only [h0, h210, h218, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h218, h7, h8, hc23, hc35, hlam, hphi]
                            · linarith only [h213, h7, h8, hc13, hc35, hlam, hphi]
                          · linarith only [h0, h211, h212, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h0, h210, h211, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
                        · linarith only [h0, h210, h224, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                          · linarith only [h0, h210, h226, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                              · linarith only [h229, h8, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                                · linarith only [h0, h208, h226, h228, h229, h231, h6, hlam, hphi, ht01, u0ehi8, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                                    · linarith only [h0, h234, h4, h7, h8, hlam, hphi, ht01, u0ehi8, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                                      · linarith only [h0, h208, h233, h234, h236, h6, hlam, hphi, ht01, u0ehi8, u1elo0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                                        · linarith only [h208, h238, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                        · rcases h1bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            rcases p240_3 (m.d 0 1) (by simp) with h242 | h242
                                            · rcases p240_3 (m.d 1 2) (by simp) with h243 | h243
                                              · linarith only [h243, hlam, p240_0]
                                              · rcases p240_3 (m.d 1 3) (by simp) with h245 | h245
                                                · linarith only [h1, h245, hlam]
                                                · linarith only [h210, h245, hlam]
                                            · linarith only [h242, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h228, h238, h7, h8, hc34, hc45, hlam, hphi, ht01, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            rcases p240_3 (m.d 0 1) (by simp) with h250 | h250
                                            · rcases p240_3 (m.d 1 2) (by simp) with h251 | h251
                                              · linarith only [h0, h251, hlam]
                                              · rcases p240_3 (m.d 1 3) (by simp) with h253 | h253
                                                · linarith only [h1, h253, hlam]
                                                · linarith only [h228, h253, hlam]
                                            · linarith only [h250, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h228, h229, h238, h7, h8, hc34, hc45, hlam, hphi, ht01, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h0, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h210, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h224, hlam, p240_1]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h226, hlam, p240_1]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h1, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h1, h238, h7, h8, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h0, h210, h234, h238, h6, h7, h8, hc14, hc45, hlam, hphi, ht01, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h229, hlam, p240_1]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h2, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h2, h238, h7, h8, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h228, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h231, hlam, p240_1]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h3, hlam, p240_0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h238, h3, h7, h8, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h0, h226, h238, h6, h7, h8, hc13, hc45, hlam, hphi, ht01, ht34, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [h0, h226, h238, h6, h7, h8, hc14, hc45, hlam, hphi, ht01, p240_1, u0ehi8, u1elo0]
                                          · obtain ⟨p240_0, p240_1, p240_2, p240_3⟩ := h240c
                                            linarith only [hlam, p240_0]
                                  · linarith only [h1, h228, h233, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h228, h7, h8, hc13, hc35, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h280 | h280
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h281 | h281
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h283 | h283
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h285 | h285
                            · linarith only [h280, h285, h7, hlam, hphi, ht01, u0ehi9, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h287 | h287
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h288 | h288
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                                  · linarith only [h0, h280, h282, h289, h7, hlam, hphi, ht01, u0ehi9, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                                    · linarith only [h0, h283, h289, h291, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h1, h287, h291, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h281, h285, h287, h288, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h280, h287, h7, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h282, h284, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h282, h283, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                        · linarith only [h0, h282, h298, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                          · linarith only [h0, h282, h300, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                            · linarith only [h280, h302, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                                  · linarith only [h0, h280, h306, h4, h7, hlam, hphi, ht01, u0ehi9, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                                        · rcases h1bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            rcases p311_3 (m.d 0 1) (by simp) with h313 | h313
                                            · rcases p311_3 (m.d 1 2) (by simp) with h314 | h314
                                              · linarith only [h314, hlam, p311_0]
                                              · rcases p311_3 (m.d 1 3) (by simp) with h316 | h316
                                                · linarith only [h1, h316, hlam]
                                                · linarith only [h282, h316, hlam]
                                            · linarith only [h313, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h304, h310, hc45, hlam, hphi, ht01, ht0b, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h302, h304, h310, hc45, hlam, hphi, ht01, ht0b, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            rcases p311_3 (m.d 0 1) (by simp) with h322 | h322
                                            · rcases p311_3 (m.d 1 2) (by simp) with h323 | h323
                                              · linarith only [h0, h323, hlam]
                                              · rcases p311_3 (m.d 1 3) (by simp) with h325 | h325
                                                · linarith only [h1, h325, hlam]
                                                · linarith only [h304, h325, hlam]
                                            · linarith only [h322, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h0, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h282, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h298, hlam, p311_1]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h300, hlam, p311_1]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h1, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h302, hlam, p311_1]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h0, h282, h300, h306, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h2, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h0, h298, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h0, h298, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h0, h298, h300, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h3, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p311_1, u1elo0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h304, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [h305, hlam, p311_0]
                                          · obtain ⟨p311_0, p311_1, p311_2, p311_3⟩ := h311c
                                            linarith only [hlam, p311_0]
                                        · linarith only [h280, h310, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                                      · linarith only [h298, h305, h309, hlam]
                                    · linarith only [h1, h304, h308, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h0, h281, h302, h304, h305, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · linarith only [h280, h282, h304, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h280, h281, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h355 | h355
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h356 | h356
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h357 | h357
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                            · linarith only [h359, h7, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                              · linarith only [h280, h361, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                                  · linarith only [h0, h356, h364, h7, hlam, hphi, ht01, u0ehi7, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                                    · linarith only [h0, h280, h357, h364, h366, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h368 | h368
                                      · linarith only [h0, h357, h368, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                      · linarith only [h0, h357, h363, h364, h368, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                                  · linarith only [h371, h7, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
                                    · linarith only [h280, h373, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                                      · linarith only [h357, h363, h375, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h377 | h377
                                        · rcases h1bigk with h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h356, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            rcases p378_3 (m.d 0 1) (by simp) with h381 | h381
                                            · rcases p378_3 (m.d 1 2) (by simp) with h382 | h382
                                              · linarith only [h0, h382, hlam]
                                              · linarith only [h356, h382, hlam]
                                            · linarith only [h381, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            rcases p378_3 (m.d 0 1) (by simp) with h386 | h386
                                            · rcases p378_3 (m.d 1 2) (by simp) with h387 | h387
                                              · linarith only [h0, h387, hlam]
                                              · linarith only [h357, h387, hlam]
                                            · linarith only [h386, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            rcases p378_3 (m.d 0 1) (by simp) with h391 | h391
                                            · rcases p378_3 (m.d 1 2) (by simp) with h392 | h392
                                              · linarith only [h0, h392, hlam]
                                              · linarith only [h358, h392, hlam]
                                            · linarith only [h391, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h0, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h0, h357, h363, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h1, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h356, hlam, p378_1]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h359, hlam, p378_1]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h361, hlam, p378_1]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h2, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h357, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h2, h356, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h363, hlam, p378_1]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h3, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h358, hlam, p378_0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h0, h356, h358, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [h0, h358, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p378_1, u1elo0]
                                          · obtain ⟨p378_0, p378_1, p378_2, p378_3⟩ := h378c
                                            linarith only [hlam, p378_0]
                                        · linarith only [h355, h377, h5, h7, hlam, hphi, u0ehi7, u0elo1]
                          · linarith only [h0, h356, h358, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h356, h357, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                        · linarith only [h0, h356, h4, h419, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
                          · linarith only [h0, h356, h4, h421, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                            · linarith only [h423, h7, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h425 | h425
                              · linarith only [h280, h425, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                                  · linarith only [h0, h4, h428, h7, hlam, hphi, ht01, u0ehi7, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h430 | h430
                                    · linarith only [h0, h280, h428, h430, h5, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                                        · rcases h1bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            rcases p434_3 (m.d 0 1) (by simp) with h436 | h436
                                            · rcases p434_3 (m.d 1 2) (by simp) with h437 | h437
                                              · linarith only [h437, hlam, p434_0]
                                              · rcases p434_3 (m.d 1 3) (by simp) with h439 | h439
                                                · linarith only [h1, h439, hlam]
                                                · linarith only [h356, h439, hlam]
                                            · linarith only [h436, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            rcases p434_3 (m.d 0 1) (by simp) with h443 | h443
                                            · rcases p434_3 (m.d 1 2) (by simp) with h444 | h444
                                              · linarith only [h0, h444, hlam]
                                              · rcases p434_3 (m.d 1 3) (by simp) with h446 | h446
                                                · linarith only [h446, hlam, p434_0]
                                                · rcases p434_3 (m.d 1 4) (by simp) with h448 | h448
                                                  · linarith only [h2, h448, hlam]
                                                  · linarith only [h423, h448, hlam]
                                            · linarith only [h443, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h427, hc45, hlam, hphi, ht01, ht0b, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            rcases p434_3 (m.d 0 1) (by simp) with h453 | h453
                                            · rcases p434_3 (m.d 1 2) (by simp) with h454 | h454
                                              · linarith only [h0, h454, hlam]
                                              · rcases p434_3 (m.d 1 3) (by simp) with h456 | h456
                                                · linarith only [h1, h456, hlam]
                                                · rcases p434_3 (m.d 1 4) (by simp) with h458 | h458
                                                  · linarith only [h2, h458, hlam]
                                                  · linarith only [h427, h458, hlam]
                                            · linarith only [h453, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h0, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h356, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h419, hlam, p434_1]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h421, hlam, p434_1]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h1, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h423, hlam, p434_1]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h425, hlam, p434_1]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h2, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h0, h419, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h0, h419, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h3, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h0, h356, h421, h432, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p434_1, u1elo0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [h427, hlam, p434_0]
                                          · obtain ⟨p434_0, p434_1, p434_2, p434_3⟩ := h434c
                                            linarith only [hlam, p434_0]
                                        · linarith only [h433, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                      · linarith only [h419, h427, h432, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                                  · linarith only [h0, h355, h356, h423, h427, h484, h5, h7, hc12, hc23, hlam, hphi, ht01, u0ehi7, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                                    · linarith only [h0, h280, h484, h486, h5, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h488 | h488
                                      · linarith only [h0, h356, h423, h427, h488, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                      · linarith only [h0, h355, h356, h484, h488, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                            · linarith only [h494, h7, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h496 | h496
                              · linarith only [h280, h496, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h498 | h498
                                · linarith only [h355, h492, h498, hlam, hphi, ht01, u0ehi8, u1elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
                                  · linarith only [h500, h7, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
                                    · linarith only [h0, h280, h492, h500, h502, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h504 | h504
                                      · linarith only [h0, h355, h492, h504, h7, hlam, hphi, ht01, u0ehi7, u1elo0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h506 | h506
                                        · linarith only [h0, h355, h493, h500, h504, h506, h7, hc23, hc34, hlam, hphi, ht01, u0ehi7, u1elo0]
                                        · linarith only [h0, h493, h500, h504, h506, h7, hc23, hc45, hlam, hphi, ht01, ht34, u0ehi7, u1elo0]
                          · linarith only [h0, h491, h493, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h0, h491, h492, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                        · linarith only [h0, h4, h491, h511, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h513 | h513
                          · linarith only [h0, h4, h491, h513, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h515 | h515
                            · linarith only [h515, h7, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h517 | h517
                              · linarith only [h280, h517, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h519 | h519
                                · linarith only [h0, h355, h5, h511, h519, h7, hlam, hphi, ht01, u0ehi7, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h521 | h521
                                  · linarith only [h0, h4, h521, h7, hlam, hphi, ht01, u0ehi7, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h523 | h523
                                    · linarith only [h0, h280, h5, h521, h523, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h525 | h525
                                      · linarith only [h0, h355, h5, h525, h7, hlam, hphi, ht01, u0ehi7, u1elo0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                                        · linarith only [h0, h355, h491, h521, h525, h527, h6, h7, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi7, u1elo0]
                                        · linarith only [h0, h491, h521, h525, h527, h6, h7, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u1elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h530 | h530
                · rcases m.htr 0 3 5 (by decide) (by decide) with h531 | h531
                  · linarith only [h4, h531, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h533 | h533
                    · linarith only [h5, h533, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                          · linarith only [h537, h6, hlam, hphi, ht01, u0ehi6, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                              · linarith only [h531, h540, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                                · linarith only [h3, h533, h535, h537, h539, h542, hlam, hphi, ht01, u0ehi8, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                                  · linarith only [h3, h535, h537, h544, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h530, h531, h544, hc23, hc35, hlam, hphi]
                            · linarith only [h530, h531, h539, hc13, hc35, hlam, hphi]
                        · linarith only [h5, h536, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h4, h535, h6, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h550 | h550
                  · linarith only [h4, h550, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h552 | h552
                    · linarith only [h5, h552, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h554 | h554
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h555 | h555
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h556 | h556
                          · linarith only [h556, h6, hlam, hphi, ht01, u0ehi6, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h558 | h558
                            · linarith only [h530, h558, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h560 | h560
                              · linarith only [h550, h560, hlam, hphi, ht01, u0ehi7, u1elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h562 | h562
                                · linarith only [h3, h530, h552, h555, h556, h562, hlam, hphi, ht01, u0ehi7, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                                  · linarith only [h530, h564, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h566 | h566
                                    · linarith only [h3, h550, h555, h556, h564, h566, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h568 | h568
                                      · linarith only [h3, h530, h552, h555, h556, h568, hlam, hphi, ht01, u0ehi7, u1elo0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                        · linarith only [h3, h5, h530, h555, h556, h564, h568, h570, h6, hc23, hc34, hlam, hphi, ht01, u0ehi7, u1elo0]
                                        · linarith only [h3, h530, h555, h556, h564, h570, hc23, hc45, hlam, hphi, ht01, ht34, u0ehi7, u1elo0]
                        · linarith only [h5, h555, h6, hc12, hc25, hlam, hphi]
                      · linarith only [h4, h554, h6, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h575 | h575
              · rcases m.htr 0 3 4 (by decide) (by decide) with h576 | h576
                · linarith only [h4, h5, h576, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h581 | h581
                        · linarith only [h5, h575, h581, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h583 | h583
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h584 | h584
                            · linarith only [h576, h578, h584, hlam, hphi, ht01, u0ehi9, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h586 | h586
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h588 | h588
                                  · linarith only [h576, h578, h588, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h590 | h590
                                    · linarith only [h2, h580, h581, h590, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h4, h5, h578, h588, h590, hc23, hc34, hlam, hphi]
                                · linarith only [h2, h579, h580, h581, h587, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h576, h578, h586, hc13, hc34, hlam, hphi]
                          · linarith only [h575, h580, h583, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h4, h5, h580, hc12, hc24, hlam, hphi]
                    · linarith only [h4, h5, h578, h579, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h599 | h599
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                        · linarith only [h5, h575, h600, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                            · linarith only [h576, h603, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h605 | h605
                              · linarith only [h2, h578, h599, h600, h605, hlam, hphi, ht01, u0ehi7, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h607 | h607
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                                  · linarith only [h576, h608, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h610 | h610
                                    · linarith only [h2, h578, h599, h600, h610, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h612 | h612
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h613 | h613
                                        · rcases h1bigk with h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h602, h610, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p614_1, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            rcases p614_3 (m.d 0 1) (by simp) with h617 | h617
                                            · rcases p614_3 (m.d 1 2) (by simp) with h618 | h618
                                              · linarith only [h0, h618, hlam]
                                              · linarith only [h599, h618, hlam]
                                            · linarith only [h617, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h5, h575, h578, h600, h602, h608, h610, hc23, hc34, hlam, hphi, ht01, p614_1, u0ehi7, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            rcases p614_3 (m.d 0 1) (by simp) with h623 | h623
                                            · rcases p614_3 (m.d 1 2) (by simp) with h624 | h624
                                              · linarith only [h0, h624, hlam]
                                              · linarith only [h602, h624, hlam]
                                            · linarith only [h623, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h0, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h0, h5, h575, h578, h608, hc13, hc34, hlam, hphi, ht01, p614_1, u0ehi7, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h600, hlam, p614_1]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h2, h600, hc15, hlam, hphi, ht01, ht0b, ht5b, p614_1, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h1, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h599, hlam, p614_1]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h603, hlam, p614_1]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h605, hlam, p614_1]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h2, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h2, h5, h575, h578, h608, hc12, hc34, hlam, hphi, ht01, ht23, p614_1, u0ehi7, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h2, h5, h575, h578, h599, h608, hc23, hc34, hlam, hphi, ht01, p614_1, u0ehi7, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h2, h5, h575, h578, h602, h608, h610, hc23, hc34, hlam, hphi, ht01, p614_1, u0ehi7, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h3, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h602, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h3, h5, h575, h578, h599, h608, hc23, hc34, hlam, hphi, ht01, p614_1, u0ehi7, u1elo0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [h607, hlam, p614_0]
                                          · obtain ⟨p614_0, p614_1, p614_2, p614_3⟩ := h614c
                                            linarith only [hlam, p614_0]
                                        · linarith only [h5, h575, h578, h602, h608, h612, h613, hlam, hphi, ht01, u0ehi7, u1elo1]
                                      · linarith only [h2, h5, h575, h578, h607, h612, hlam, hphi, ht01, u0ehi7, u1elo0]
                                · linarith only [h598, h600, h602, h607, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h575, h599, h602, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h4, h5, h599, hc12, hc24, hlam, hphi]
                    · linarith only [h5, h575, h598, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h654 | h654
                · linarith only [h4, h5, h654, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
                  · linarith only [h4, h575, h656, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
                        · linarith only [h5, h660, hlam, hphi, ht01, u0ehi6, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h662 | h662
                          · linarith only [h2, h4, h575, h660, h662, hlam, hphi, ht01, u0ehi7, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                            · linarith only [h654, h664, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                              · linarith only [h2, h656, h659, h660, h666, hlam, hphi, ht01, u0ehi7, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h669 | h669
                                  · linarith only [h2, h654, h659, h662, h668, h669, hlam, hphi, ht01, u0ehi7, u1elo0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h671 | h671
                                    · linarith only [h2, h656, h659, h662, h668, h671, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h673 | h673
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h674 | h674
                                        · rcases h1bigk with h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c | h675c
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h659, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p675_1, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            rcases p675_3 (m.d 0 1) (by simp) with h678 | h678
                                            · rcases p675_3 (m.d 1 2) (by simp) with h679 | h679
                                              · linarith only [h0, h679, hlam]
                                              · linarith only [h659, h679, hlam]
                                            · linarith only [h678, hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h4, h575, h659, h660, h669, h673, hc23, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h4, h575, h659, h662, h669, h673, hc23, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h0, hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h0, h4, h575, h669, h673, hc13, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h660, hlam, p675_1]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h662, hlam, p675_1]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h1, hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h659, hlam, p675_1]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h664, hlam, p675_1]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h666, hlam, p675_1]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h2, hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h2, h4, h575, h669, h673, hc12, hc34, hlam, hphi, ht01, ht23, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h2, h4, h575, h659, h669, h673, hc23, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h2, h4, h575, h659, h662, h669, h673, hc23, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h3, hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h4, h575, h659, h669, h673, hc23, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo4]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h3, h4, h575, h659, h669, h673, hc23, hc34, hlam, hphi, ht01, p675_1, u0ehi7, u1elo0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [h668, hlam, p675_0]
                                          · obtain ⟨p675_0, p675_1, p675_2, p675_3⟩ := h675c
                                            linarith only [hlam, p675_0]
                                        · linarith only [h4, h575, h669, h673, h674, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                      · linarith only [h2, h668, h673, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h2, h658, h659, h660, h668, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h4, h5, h659, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h709 | h709
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h710 | h710
                        · linarith only [h4, h5, h710, hlam, hphi, ht01, u0ehi7, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
                          · linarith only [h2, h4, h575, h710, h712, hlam, hphi, ht01, u0ehi7, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h714 | h714
                            · linarith only [h654, h714, hlam, hphi, ht01, u0ehi7, u1elo2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                              · linarith only [h2, h656, h709, h710, h716, hlam, hphi, ht01, u0ehi7, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                                · linarith only [h2, h4, h5, h658, h718, hlam, hphi, ht01, u0ehi7, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h720 | h720
                                  · linarith only [h654, h720, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h722 | h722
                                    · linarith only [h3, h656, h709, h710, h718, h722, hlam, hphi, ht01, u0ehi7, u1elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h724 | h724
                                      · linarith only [h4, h5, h658, h724, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                                      · linarith only [h3, h4, h5, h709, h710, h718, h724, hc23, hc45, hlam, hphi, ht01, ht34, u0ehi7, u1elo0]
                      · linarith only [h4, h5, h709, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h728 | h728
            · rcases m.htr 0 2 5 (by decide) (by decide) with h729 | h729
              · rcases m.htr 0 3 4 (by decide) (by decide) with h730 | h730
                · rcases m.htr 0 3 5 (by decide) (by decide) with h731 | h731
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                      · linarith only [h4, h728, h733, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h738 | h738
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h741 | h741
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h742 | h742
                                      · linarith only [h0, h735, h742, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                      · linarith only [h1, h733, h735, h739, h742, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h4, h728, h732, h741, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                  · linarith only [h4, h728, h732, h740, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h747 | h747
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h748 | h748
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h749 | h749
                                      · linarith only [h735, h739, h749, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h751 | h751
                                        · linarith only [h735, h739, h747, h751, hlam]
                                        · rcases h1bigk with h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h736, hc25, hlam, hphi, ht01, ht0b, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h733, h736, h748, hc35, hlam, hphi, ht01, ht0b, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            rcases p753_3 (m.d 0 1) (by simp) with h757 | h757
                                            · rcases p753_3 (m.d 1 2) (by simp) with h758 | h758
                                              · linarith only [h0, h758, hlam]
                                              · linarith only [h735, h758, hlam]
                                            · linarith only [h757, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            rcases p753_3 (m.d 0 1) (by simp) with h762 | h762
                                            · rcases p753_3 (m.d 1 2) (by simp) with h763 | h763
                                              · linarith only [h0, h763, hlam]
                                              · linarith only [h736, h763, hlam]
                                            · linarith only [h762, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h0, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h733, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h0, h735, h747, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h1, h733, hc15, hlam, hphi, ht01, ht0b, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h1, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h1, h735, h747, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h1, h736, h747, h749, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h2, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h735, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h737, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h739, hlam, p753_1]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h3, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h736, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h738, hlam, p753_0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [h3, h735, h747, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p753_1, u1elo0]
                                          · obtain ⟨p753_0, p753_1, p753_2, p753_3⟩ := h753c
                                            linarith only [hlam, p753_0]
                                    · linarith only [h4, h728, h732, h735, h739, h747, h748, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · linarith only [h4, h728, h732, h735, h739, h747, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h1, h731, h733, h735, h738, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h1, h730, h733, h735, h737, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h4, h729, h735, h736, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h4, h728, h735, hc12, hc23, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
                      · linarith only [h4, h728, h793, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h795 | h795
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h796 | h796
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                                · linarith only [h732, h799, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h801 | h801
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h802 | h802
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h803 | h803
                                      · linarith only [h732, h795, h803, hlam, hphi, ht01, u0ehi8, u1elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h805 | h805
                                        · linarith only [h1, h732, h793, h796, h801, h803, h805, hlam, hphi, ht01, u0ehi8, u1elo0]
                                        · rcases h1bigk with h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h796, h803, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h793, h796, h801, h803, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            rcases p807_3 (m.d 0 1) (by simp) with h811 | h811
                                            · rcases p807_3 (m.d 1 2) (by simp) with h812 | h812
                                              · linarith only [h0, h812, hlam]
                                              · linarith only [h795, h812, hlam]
                                            · linarith only [h811, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            rcases p807_3 (m.d 0 1) (by simp) with h816 | h816
                                            · rcases p807_3 (m.d 1 2) (by simp) with h817 | h817
                                              · linarith only [h0, h817, hlam]
                                              · linarith only [h796, h817, hlam]
                                            · linarith only [h816, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h0, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h793, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h1, h793, hc15, hlam, hphi, ht01, ht0b, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h1, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h1, h795, h801, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h1, h796, h801, h803, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h2, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h795, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h797, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h799, hlam, p807_1]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h3, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h796, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h798, hlam, p807_0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [h3, h795, h801, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
                                          · obtain ⟨p807_0, p807_1, p807_2, p807_3⟩ := h807c
                                            linarith only [hlam, p807_0]
                                    · linarith only [h4, h729, h732, h802, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                  · linarith only [h4, h729, h732, h801, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                              · linarith only [h1, h731, h793, h796, h798, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h1, h730, h793, h795, h797, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h729, h795, h796, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h4, h728, h795, hc12, hc23, hlam, hphi]
                  · linarith only [h4, h729, h731, hlam]
                · linarith only [h4, h728, h730, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h849 | h849
                · rcases m.htr 0 3 5 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h851 | h851
                    · linarith only [h728, h729, h851, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
                      · linarith only [h0, h4, h853, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h855 | h855
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h856 | h856
                          · linarith only [h728, h729, h856, hlam, hphi, ht01, u0ehi8, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h858 | h858
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h859 | h859
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h860 | h860
                                · linarith only [h851, h860, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h862 | h862
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h864 | h864
                                      · linarith only [h851, h864, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h866 | h866
                                        · linarith only [h728, h729, h864, h866, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                        · rcases h1bigk with h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c | h868c
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h728, h729, h855, h864, hc24, hc45, hlam, hphi, ht01, p868_1, u0ehi8, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h859, hc35, hlam, hphi, ht01, ht0b, ht5b, p868_1, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            rcases p868_3 (m.d 0 1) (by simp) with h872 | h872
                                            · rcases p868_3 (m.d 1 2) (by simp) with h873 | h873
                                              · linarith only [h0, h873, hlam]
                                              · linarith only [h855, h873, hlam]
                                            · linarith only [h872, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h728, h729, h855, h856, h862, h864, hc34, hc45, hlam, hphi, ht01, p868_1, u0ehi8, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h0, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h853, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h0, h728, h729, h864, hc14, hc45, hlam, hphi, ht01, p868_1, u0ehi8, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h856, hlam, p868_1]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h1, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h1, h728, h729, h864, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p868_1, u0ehi8, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h1, h728, h729, h855, h862, h864, hc34, hc45, hlam, hphi, ht01, p868_1, u0ehi8, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p868_1, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h2, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h855, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h858, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h860, hlam, p868_1]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h3, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h728, h729, h855, h862, h864, hc34, hc45, hlam, hphi, ht01, p868_1, u0ehi8, u1elo4]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h859, hlam, p868_0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [h1, h728, h729, h855, h859, h862, h864, hc34, hc45, hlam, hphi, ht01, p868_1, u0ehi8, u1elo0]
                                          · obtain ⟨p868_0, p868_1, p868_2, p868_3⟩ := h868c
                                            linarith only [hlam, p868_0]
                                    · linarith only [h4, h728, h863, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                  · linarith only [h4, h728, h862, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                              · linarith only [h850, h853, h855, h859, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1, h849, h853, h855, h858, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h4, h728, h855, hc12, hc23, hlam, hphi]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h903 | h903
                    · linarith only [h4, h728, h850, h903, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
                      · linarith only [h0, h4, h905, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h907 | h907
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h908 | h908
                          · linarith only [h1, h728, h729, h905, h908, hlam, hphi, ht01, u0ehi8, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h910 | h910
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h911 | h911
                              · linarith only [h1, h850, h911, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h913 | h913
                                · linarith only [h903, h913, hlam, hphi, ht01, u0ehi8, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h916 | h916
                                    · linarith only [h4, h728, h850, h916, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                                    · linarith only [h4, h728, h916, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                  · linarith only [h4, h728, h915, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                            · linarith only [h849, h905, h907, h910, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h4, h728, h907, hc12, hc23, hlam, hphi]
                · linarith only [h4, h728, h849, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h923 | h923
              · rcases m.htr 0 3 4 (by decide) (by decide) with h924 | h924
                · rcases m.htr 0 3 5 (by decide) (by decide) with h925 | h925
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h927 | h927
                      · linarith only [h4, h923, h927, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
                        · linarith only [h1, h728, h923, h927, h929, hlam, hphi, ht01, u0ehi9, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h933 | h933
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h935 | h935
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h936 | h936
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h937 | h937
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h938 | h938
                                        · linarith only [h1, h932, h938, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                        · linarith only [h1, h932, h934, h938, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · linarith only [h1, h728, h923, h932, h934, h937, hlam, hphi, ht01, u0ehi9, u1elo0]
                                    · linarith only [h728, h923, h935, h936, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                  · linarith only [h4, h923, h935, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                · linarith only [h924, h926, h929, h931, h934, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h1, h925, h929, h931, h932, h933, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h1, h924, h927, h931, h932, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h4, h923, h931, hc12, hc23, hlam, hphi]
                    · linarith only [h728, h923, h926, hlam]
                  · linarith only [h4, h923, h925, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h950 | h950
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h951 | h951
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h952 | h952
                      · linarith only [h4, h923, h952, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h954 | h954
                        · linarith only [h728, h923, h954, hlam, hphi, ht01, u0ehi9, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h956 | h956
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h957 | h957
                            · linarith only [h1, h4, h923, h924, h957, hlam, hphi, u0ehi9, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h959 | h959
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h960 | h960
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h961 | h961
                                  · linarith only [h4, h923, h924, h961, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                                  · linarith only [h4, h923, h961, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                · linarith only [h951, h952, h956, h957, h960, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h950, h952, h956, h959, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h4, h923, h956, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h923, h924, h951, hlam]
                  · linarith only [h4, h923, h950, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h969 | h969
                · rcases m.htr 0 3 5 (by decide) (by decide) with h970 | h970
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h971 | h971
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h972 | h972
                      · linarith only [h4, h972, hlam, hphi, ht01, u0ehi6, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h974 | h974
                        · linarith only [h728, h974, hlam, hphi, ht01, u0ehi6, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h976 | h976
                          · linarith only [h1, h923, h972, h976, hlam, hphi, ht01, u0ehi6, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h979 | h979
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h980 | h980
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h981 | h981
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h982 | h982
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h984 | h984
                                        · linarith only [h1, h978, h984, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                        · linarith only [h1, h978, h980, h984, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                      · linarith only [h1, h978, h980, h983, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h1, h728, h979, h981, h982, hlam, hphi, ht01, u0ehi6, u1elo0]
                                  · linarith only [h4, h981, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h990 | h990
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h992 | h992
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h993 | h993
                                        · linarith only [h978, h980, h993, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                        · rcases h1bigk with h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            rcases p995_3 (m.d 0 1) (by simp) with h997 | h997
                                            · rcases p995_3 (m.d 1 2) (by simp) with h998 | h998
                                              · linarith only [h998, hlam, p995_0]
                                              · rcases p995_3 (m.d 1 3) (by simp) with h1000 | h1000
                                                · linarith only [h1, h1000, hlam]
                                                · linarith only [h1000, h972, hlam]
                                            · linarith only [h997, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h978, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p995_1, u1elo0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            rcases p995_3 (m.d 0 1) (by simp) with h1005 | h1005
                                            · rcases p995_3 (m.d 1 2) (by simp) with h1006 | h1006
                                              · linarith only [h0, h1006, hlam]
                                              · rcases p995_3 (m.d 1 3) (by simp) with h1008 | h1008
                                                · linarith only [h1, h1008, hlam]
                                                · linarith only [h1008, h978, hlam]
                                            · linarith only [h1005, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            rcases p995_3 (m.d 0 1) (by simp) with h1012 | h1012
                                            · rcases p995_3 (m.d 1 2) (by simp) with h1013 | h1013
                                              · linarith only [h0, h1013, hlam]
                                              · rcases p995_3 (m.d 1 3) (by simp) with h1015 | h1015
                                                · linarith only [h1, h1015, hlam]
                                                · linarith only [h1015, h979, hlam]
                                            · linarith only [h1012, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h0, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h972, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h974, hlam, p995_1]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h976, hlam, p995_1]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h1, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p995_1, u1elo0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h1, h974, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p995_1, u1elo0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h1, h974, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p995_1, u1elo0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h2, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h980, hc12, hc45, hlam, hphi, ht23, ht34, p995_1]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h978, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h980, hlam, p995_1]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h3, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p995_1, u1elo0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h979, hlam, p995_0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p995_1, u1elo0]
                                          · obtain ⟨p995_0, p995_1, p995_2, p995_3⟩ := h995c
                                            linarith only [hlam, p995_0]
                                      · linarith only [h1, h728, h969, h971, h992, hlam, hphi, ht01, u0ehi6, u1elo0]
                                    · linarith only [h1, h728, h979, h990, h991, hlam, hphi, ht01, u0ehi6, u1elo0]
                                  · linarith only [h4, h990, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                              · linarith only [h1, h970, h978, h979, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
                              · linarith only [h1, h1043, h969, h978, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1045 | h1045
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1046 | h1046
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1047 | h1047
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1048 | h1048
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1049 | h1049
                                        · rcases h1bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            rcases p1050_3 (m.d 0 1) (by simp) with h1052 | h1052
                                            · rcases p1050_3 (m.d 1 2) (by simp) with h1053 | h1053
                                              · linarith only [h1053, hlam, p1050_0]
                                              · rcases p1050_3 (m.d 1 3) (by simp) with h1055 | h1055
                                                · linarith only [h1, h1055, hlam]
                                                · linarith only [h1055, h972, hlam]
                                            · linarith only [h1052, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            rcases p1050_3 (m.d 0 1) (by simp) with h1059 | h1059
                                            · rcases p1050_3 (m.d 1 2) (by simp) with h1060 | h1060
                                              · linarith only [h0, h1060, hlam]
                                              · rcases p1050_3 (m.d 1 3) (by simp) with h1062 | h1062
                                                · linarith only [h1062, hlam, p1050_0]
                                                · rcases p1050_3 (m.d 1 4) (by simp) with h1064 | h1064
                                                  · linarith only [h1064, h2, hlam]
                                                  · linarith only [h1064, h978, hlam]
                                            · linarith only [h1059, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1045, hc45, hlam, hphi, ht01, ht0b, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            rcases p1050_3 (m.d 0 1) (by simp) with h1069 | h1069
                                            · rcases p1050_3 (m.d 1 2) (by simp) with h1070 | h1070
                                              · linarith only [h0, h1070, hlam]
                                              · rcases p1050_3 (m.d 1 3) (by simp) with h1072 | h1072
                                                · linarith only [h1, h1072, hlam]
                                                · rcases p1050_3 (m.d 1 4) (by simp) with h1074 | h1074
                                                  · linarith only [h1074, h2, hlam]
                                                  · linarith only [h1045, h1074, hlam]
                                            · linarith only [h1069, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h0, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h972, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h974, hlam, p1050_1]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h976, hlam, p1050_1]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1, h1043, h1049, h969, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h978, hlam, p1050_1]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1043, hlam, p1050_1]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h2, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1, h969, h978, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1, h969, h978, hc15, hlam, hphi, ht01, ht0b, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h3, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1, h1043, h1049, h969, h972, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1050_1, u1elo0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [h1045, hlam, p1050_0]
                                          · obtain ⟨p1050_0, p1050_1, p1050_2, p1050_3⟩ := h1050c
                                            linarith only [hlam, p1050_0]
                                        · linarith only [h1, h1049, h969, h971, h972, h978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                      · linarith only [h1045, h1048, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                    · linarith only [h1046, h1047, h728, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                                  · linarith only [h1, h1046, h4, h969, hlam, hphi, ht01, u0ehi6, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1102 | h1102
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1103 | h1103
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1104 | h1104
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1105 | h1105
                                        · linarith only [h1, h1045, h1105, h969, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                        · linarith only [h1, h1105, h969, h971, h972, h978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                      · linarith only [h1, h1104, h728, h969, h971, hlam, hphi, ht01, u0ehi6, u1elo0]
                                    · linarith only [h1, h1102, h1103, h728, h970, hlam, hphi, ht01, u0ehi6, u1elo0]
                                  · linarith only [h1102, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
                      · linarith only [h1111, h4, hlam, hphi, ht01, u0ehi6, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1113 | h1113
                        · linarith only [h1, h1111, h1113, h728, hlam, hphi, ht01, u0ehi6, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
                          · linarith only [h1, h1111, h1115, h923, hlam, hphi, ht01, u0ehi6, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1117 | h1117
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1118 | h1118
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1119 | h1119
                                · linarith only [h1, h1117, h1119, h971, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1121 | h1121
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1122 | h1122
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1123 | h1123
                                      · linarith only [h1121, h1123, h728, h971, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                      · linarith only [h1123, h728, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                                    · linarith only [h1, h1118, h1122, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h1, h1117, h1121, h4, hlam, hphi, ht01, u0ehi6, u1elo0]
                              · linarith only [h1, h1117, h1118, h970, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1129 | h1129
                              · linarith only [h1, h1117, h1129, h969, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1131 | h1131
                                · linarith only [h1131, h728, h971, hlam, hphi, ht01, u0ehi6, u1elo3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1134 | h1134
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1135 | h1135
                                      · linarith only [h1133, h1135, h728, h971, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                      · linarith only [h1, h1111, h1117, h1135, h728, h969, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi6, u1elo0]
                                    · linarith only [h1, h1134, h4, h970, hlam, hphi, ht01, u0ehi6, u1elo0]
                                  · linarith only [h1, h1133, h4, h969, hlam, hphi, ht01, u0ehi6, u1elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1140 | h1140
                    · linarith only [h1140, h969, h970, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1142 | h1142
                      · linarith only [h1142, h4, hlam, hphi, ht01, u0ehi6, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1144 | h1144
                        · linarith only [h1144, h728, hlam, hphi, ht01, u0ehi6, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
                          · linarith only [h1, h1142, h1146, h923, hlam, hphi, ht01, u0ehi6, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1149 | h1149
                              · linarith only [h1, h1149, h970, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1151 | h1151
                                · linarith only [h1140, h1148, h1149, h1151, h3, h728, hlam, hphi, ht01, u0ehi6, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1153 | h1153
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1154 | h1154
                                    · linarith only [h1154, h728, h969, h970, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                    · linarith only [h1154, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                                  · linarith only [h1148, h1149, h1153, h3, h4, hlam, hphi, ht01, u0ehi6, u1elo0]
                            · linarith only [h1148, h969, h970, hc13, hc35, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1159 | h1159
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1160 | h1160
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
                      · linarith only [h1161, h4, hlam, hphi, ht01, u0ehi6, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1163 | h1163
                        · linarith only [h1, h1161, h1163, h728, hlam, hphi, ht01, u0ehi6, u1elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1165 | h1165
                          · linarith only [h1, h1161, h1165, h923, hlam, hphi, ht01, u0ehi6, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1167 | h1167
                            · linarith only [h1, h1167, h969, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1169 | h1169
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1170 | h1170
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1171 | h1171
                                  · linarith only [h1159, h1171, h923, h969, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                  · linarith only [h1171, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                                · linarith only [h1160, h1167, h1169, h1170, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h1159, h1169, h969, hc13, hc34, hlam, hphi]
                    · linarith only [h1159, h1160, h969, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1177 | h1177
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1178 | h1178
                      · linarith only [h1178, h4, hlam, hphi, ht01, u0ehi6, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1180 | h1180
                        · linarith only [h1, h1178, h1180, h728, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1182 | h1182
                          · linarith only [h1, h1178, h1182, h923, hlam, hphi, ht01, u0ehi6, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1184 | h1184
                            · linarith only [h1, h1184, h969, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1186 | h1186
                              · linarith only [h1159, h1184, h1186, h2, h4, hlam, hphi, ht01, u0ehi6, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1188 | h1188
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1189 | h1189
                                  · linarith only [h1189, h4, h969, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                  · linarith only [h1189, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1192 | h1192
                                  · linarith only [h1192, h4, h969, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                  · linarith only [h1177, h1178, h1184, h1188, h1192, h2, h4, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi6, u1elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1195 | h1195
                      · linarith only [h1195, h4, hlam, hphi, ht01, u0ehi6, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1197 | h1197
                        · linarith only [h1197, h728, hlam, hphi, ht01, u0ehi6, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
                          · linarith only [h1, h1195, h1199, h923, hlam, hphi, ht01, u0ehi6, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1201 | h1201
                            · linarith only [h1, h1201, h4, h969, hlam, hphi, ht01, u0ehi6, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1203 | h1203
                              · linarith only [h1159, h1201, h1203, h2, h4, hlam, hphi, ht01, u0ehi6, u1elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1205 | h1205
                                · linarith only [h1177, h1205, h2, h4, h969, hlam, hphi, ht01, u0ehi6, u1elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1207 | h1207
                                  · linarith only [h1207, h4, h969, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                  · linarith only [h1207, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
        · linarith only [h3, hlam, hphi, ht01, u0ehi5, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi6, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

end R2N4
