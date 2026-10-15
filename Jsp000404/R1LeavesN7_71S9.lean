import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_IR_L_R_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h10, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc01, hlam, hphi, p12_1, u0ehi1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc01, hlam, hphi, p12_1, u0ehi4]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc02, hlam, hphi, p12_1, u0ehi0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h3, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, hlam, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h1, hlam, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h5, hc03, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, h10, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc04, hlam, hphi, p12_1, u0ehi0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h3, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h3, h5, hc03, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi3]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc05, hlam, hphi, p12_1, u0ehi0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h3, h5, hc03, hlam, hphi, p12_1, u0ehi1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h4, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h5, hlam, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                  · linarith only [h0, h4, h8, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h0, h39, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h0, h41, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h1, h3, h41, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h3, h41, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h41, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hc01, hlam, hphi, p43_1, u0ehi4]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hc02, hlam, hphi, p43_1, u0ehi0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h3, h41, h5, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h41, h5, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h41, h5, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h0, hlam, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h1, hlam, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h0, h41, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h0, h41, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hc04, hlam, hphi, p43_1, u0ehi0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h2, hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h3, hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h0, h3, h41, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hc05, hlam, hphi, p43_1, u0ehi0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h0, h3, h5, hc01, hlam, hphi, p43_1, u0ehi1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h4, hlam, p43_0]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [h5, hlam, p43_1]
                      · have p43_0 := h43c.1
                        have p43_1 := h43c.2.1
                        have p43_2 := h43c.2.2.1
                        have p43_3 := h43c.2.2.2
                        linarith only [hlam, p43_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                · linarith only [h69, h7, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                    · linarith only [h0, h3, h6, h7, h71, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h7, h72, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                    · rcases h0bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hc01, hlam, hphi, p76_1, u0ehi1]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h3, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p76_1, u1ehi2]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hc01, hlam, hphi, p76_1, u0ehi3]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hc01, hlam, hphi, p76_1, u0ehi4]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hc02, hlam, hphi, p76_1, u0ehi0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h3, h7, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p76_1, u1ehi2]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h3, h7, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p76_1, u1ehi2]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hc02, hlam, hphi, p76_1, u0ehi4]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h0, hlam, p76_1]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h1, hlam, p76_1]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h0, h3, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p76_1, u1ehi2]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, p76_1, u0ehi4]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hc04, hlam, hphi, p76_1, u0ehi0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h2, hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h3, hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h0, h3, hc01, hlam, hphi, p76_1, u0ehi4]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h0, h3, h7, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p76_1, u1ehi2]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h0, h3, h5, hc01, hlam, hphi, p76_1, u0ehi1]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h4, hlam, p76_0]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [h5, hlam, p76_1]
                      · have p76_0 := h76c.1
                        have p76_1 := h76c.2.1
                        have p76_2 := h76c.2.2.1
                        have p76_3 := h76c.2.2.2
                        linarith only [hlam, p76_0]
                    · linarith only [h7, h75, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h1, h103, h106, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hc01, hlam, hphi, p108_1, u0ehi1]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h106, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h106, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hc01, hlam, hphi, p108_1, u0ehi4]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hc02, hlam, hphi, p108_1, u0ehi0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h106, h3, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h106, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h106, h5, hc02, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h0, hlam, p108_1]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h1, hlam, p108_1]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h0, h106, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h0, h106, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hc04, hlam, hphi, p108_1, u0ehi0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h2, hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h3, hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h0, h106, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi3]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hc05, hlam, hphi, p108_1, u0ehi0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h0, h3, h5, hc01, hlam, hphi, p108_1, u0ehi1]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h4, hlam, p108_0]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [h5, hlam, p108_1]
                      · have p108_0 := h108c.1
                        have p108_1 := h108c.2.1
                        have p108_2 := h108c.2.2.1
                        have p108_3 := h108c.2.2.2
                        linarith only [hlam, p108_0]
                  · linarith only [h105, h6, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h103, h104, h6, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                · linarith only [h103, h136, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h0, h136, h3, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
            · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
              · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                    · linarith only [h139, h141, h143, h5, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c | h145c
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc01, hlam, hphi, p145_1, u0ehi1]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc01, hlam, hphi, p145_1, u0ehi2]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc01, hlam, hphi, p145_1, u0ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h5, hc01, hlam, hphi, p145_1, u0ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc02, hlam, hphi, p145_1, u0ehi0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc02, hlam, hphi, p145_1, u0ehi2]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc02, hlam, hphi, p145_1, u0ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h5, hc02, hlam, hphi, p145_1, u0ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h0, hlam, p145_1]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h1, hlam, p145_1]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hc03, hlam, hphi, p145_1, u0ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h0, h5, hc01, hlam, hphi, p145_1, u0ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, ht12, ht23, ht34, p145_1, u1ehi0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h2, hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h3, hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h5, hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h0, h139, h142, h143, hc05, hlam, hphi, ht0b, ht45, ht5b, p145_1, u4ehi3]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h4, hc03, hlam, hphi, p145_1, u0ehi1]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h4, hlam, p145_0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, p145_1, u4ehi0]
                      · have p145_0 := h145c.1
                        have p145_1 := h145c.2.1
                        have p145_2 := h145c.2.2.1
                        have p145_3 := h145c.2.2.2
                        linarith only [hlam, p145_0]
                  · linarith only [h0, h141, h142, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h172 | h172
                  · linarith only [h0, h140, h141, h172, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                    · linarith only [h0, h140, h174, h5, hc01, hlam, hphi, u0ehi4]
                    · rcases h0bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hc01, hlam, hphi, p176_1, u0ehi1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hc01, hlam, hphi, p176_1, u0ehi2]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hc01, hlam, hphi, p176_1, u0ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h5, hc01, hlam, hphi, p176_1, u0ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h0, h140, h141, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h0, h140, h141, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hc02, hlam, hphi, p176_1, u0ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h5, hc02, hlam, hphi, p176_1, u0ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h0, hlam, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, hlam, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hc03, hlam, hphi, p176_1, u0ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h0, h5, hc01, hlam, hphi, p176_1, u0ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, ht12, ht23, ht34, p176_1, u1ehi0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h2, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h3, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h5, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h0, h140, h141, h4, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p176_1, u0ehi1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h4, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, p176_1, u4ehi0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
              · linarith only [h140, h3, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
              · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                    · linarith only [h1, h139, h203, h206, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h1, h139, h203, hc01, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h1, h139, h203, hc01, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hc01, hlam, hphi, p208_1, u0ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hc01, hlam, hphi, p208_1, u0ehi4]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hc02, hlam, hphi, p208_1, u0ehi0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h1, h139, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p208_1, u1ehi1]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hc02, hlam, hphi, p208_1, u0ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h5, hc02, hlam, hphi, p208_1, u0ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h0, hlam, p208_1]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h1, hlam, p208_1]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hc03, hlam, hphi, p208_1, u0ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h0, h5, hc01, hlam, hphi, p208_1, u0ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, ht12, ht23, ht34, p208_1, u1ehi0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h2, hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h3, hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h5, hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h0, h203, hc05, hlam, hphi, ht0b, ht45, ht5b, p208_1, u4ehi3]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h4, hc03, hlam, hphi, p208_1, u0ehi1]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h4, hlam, p208_0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [h5, hc45, hlam, hphi, p208_1, u4ehi0]
                      · have p208_0 := h208c.1
                        have p208_1 := h208c.2.1
                        have p208_2 := h208c.2.2.1
                        have p208_3 := h208c.2.2.2
                        linarith only [hlam, p208_0]
                  · linarith only [h139, h205, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h139, h203, h204, hc13, hlam, hphi, u1ehi1]
              · linarith only [h203, h3, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
          · linarith only [h237, h3, h4, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
            · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
              · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
                · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h239, h242, h4, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                    · linarith only [h237, h244, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h0, h239, h241, h244, h4, hc45, hlam, hphi, u4ehi3]
                · linarith only [h0, h240, h241, h4, hc23, hc35, hlam, hphi]
              · linarith only [h240, h3, h4, hc35, hlam, hphi, ht12, ht23, u1ehi2]
            · linarith only [h1, h239, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
        · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
          · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
            · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
              · linarith only [h0, h253, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                · linarith only [h0, h252, h255, h3, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                    · rcases h0bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hlam, p259_0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h2, h255, h257, h258, hc01, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, hc01, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hc01, hlam, hphi, p259_1, u0ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hc02, hlam, hphi, p259_1, u0ehi0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hlam, p259_0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, hc02, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, h3, hc02, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hc02, hlam, hphi, p259_1, u0ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, hlam, p259_1]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h1, hlam, p259_1]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hlam, p259_0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h3, hlam, p259_1]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, p259_1, u0ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, hc04, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h2, hlam, p259_0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hlam, p259_0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, p259_1, u0ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h0, h252, h257, h258, hc05, hlam, hphi, ht0b, ht45, ht5b, p259_1, u4ehi4]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h250, hc03, hlam, hphi, p259_1, u0ehi1]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h250, hlam, p259_0]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [h251, hlam, p259_1]
                      · have p259_0 := h259c.1
                        have p259_1 := h259c.2.1
                        have p259_2 := h259c.2.2.1
                        have p259_3 := h259c.2.2.2
                        linarith only [hlam, p259_0]
                    · linarith only [h258, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · linarith only [h250, h257, h3, hc23, hc34, hlam, hphi]
            · linarith only [h1, h252, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h250, h251, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
          · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
            · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
              · linarith only [h0, h291, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h293 | h293
                · linarith only [h0, h290, h293, h3, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h295 | h295
                  · linarith only [h0, h250, h290, h295, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h297 | h297
                    · rcases h0bigk with h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hlam, p298_0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hc01, hlam, hphi, p298_1, u0ehi1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hc01, hlam, hphi, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h250, h289, hc01, hlam, hphi, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h250, hc01, hlam, hphi, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hc02, hlam, hphi, p298_1, u0ehi0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hlam, p298_0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hc02, hlam, hphi, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h250, h289, hc02, hlam, hphi, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h250, hc02, hlam, hphi, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h0, hlam, p298_1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h1, hlam, p298_1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hlam, p298_0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h3, hlam, p298_1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h250, hlam, p298_1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hc04, hlam, hphi, p298_1, u0ehi0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h2, hlam, p298_0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hlam, p298_0]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h250, h3, hc34, hlam, hphi, ht01, ht12, ht23, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p298_1, u1ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h289, h3, hc34, hlam, hphi, ht01, ht12, ht23, p298_1, u0ehi1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h289, h3, hc34, hlam, hphi, ht01, ht12, ht23, p298_1, u0ehi2]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [h289, hlam, p298_1]
                      · have p298_0 := h298c.1
                        have p298_1 := h298c.2.1
                        have p298_2 := h298c.2.2.1
                        have p298_3 := h298c.2.2.2
                        linarith only [hlam, p298_0]
                    · linarith only [h289, h297, h3, hlam]
            · linarith only [h1, h290, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
            · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
              · linarith only [h0, h289, h3, h327, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h329 | h329
                · linarith only [h3, h326, h329, hc12, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                  · linarith only [h0, h250, h326, h331, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h333 | h333
                    · linarith only [h289, h3, h333, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                    · linarith only [h3, h333, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
            · linarith only [h1, h3, h326, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
      · linarith only [h1, h2, h337, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
        · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
          · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
            · rcases m.htr 1 3 4 (by decide) (by decide) with h342 | h342
              · linarith only [h0, h337, h342, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                · linarith only [h1, h2, h337, h344, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                    · linarith only [h1, h2, h344, h346, h347, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h1, h2, h344, h347, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1, h2, h339, h344, h346, hc23, hc34, hlam, hphi]
            · linarith only [h1, h2, h341, hc24, hlam, hphi, ht12, u1ehi1]
          · linarith only [h1, h2, h339, h340, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
          · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
            · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
              · linarith only [h337, h355, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                · linarith only [h1, h337, h357, hc02, hlam, hphi, u0ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                  · linarith only [h1, h2, h339, h357, h359, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h361 | h361
                    · rcases h0bigk with h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hlam, p362_0]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hc01, hlam, hphi, p362_1, u0ehi1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hc01, hlam, hphi, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hc01, hlam, hphi, p362_1, u0ehi3]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h339, hc01, hlam, hphi, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hc02, hlam, hphi, p362_1, u0ehi0]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hlam, p362_0]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, hc04, hlam, hphi, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, hlam, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, h339, h357, hc34, hlam, hphi, ht01, ht12, ht23, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h0, hlam, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h1, hlam, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hlam, p362_0]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h337, hlam, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h339, hlam, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, h357, hc34, hlam, hphi, ht12, ht23, p362_1, u1ehi0]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h1, h2, h357, hc23, hc34, hlam, hphi, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, h357, hc34, hlam, hphi, ht01, ht12, ht23, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hlam, p362_0]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, h339, h357, hc34, hlam, hphi, ht01, ht12, ht23, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p362_1, u1ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h1, h2, h353, h357, hc34, hlam, hphi, ht01, ht12, ht23, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h2, h353, h357, hc34, hlam, hphi, ht01, ht12, ht23, p362_1, u0ehi2]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [h353, hlam, p362_1]
                      · have p362_0 := h362c.1
                        have p362_1 := h362c.2.1
                        have p362_2 := h362c.2.2.1
                        have p362_3 := h362c.2.2.2
                        linarith only [hlam, p362_0]
                    · linarith only [h2, h353, h357, h361, hlam]
            · linarith only [h1, h2, h354, hc24, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
            · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
              · linarith only [h0, h1, h2, h353, h391, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                · linarith only [h1, h2, h337, h353, h393, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                  · linarith only [h1, h2, h339, h353, h395, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h397 | h397
                    · linarith only [h1, h2, h353, h397, hc23, hc34, hlam, hphi]
                    · linarith only [h337, h397, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
            · linarith only [h1, h2, h390, hc24, hlam, hphi, ht12, u1ehi1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h401 | h401
    · rcases m.htr 0 3 4 (by decide) (by decide) with h402 | h402
      · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
        · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
          · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
            · linarith only [h1, h401, h404, h405, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
              · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
                    · linarith only [h1, h401, h408, h410, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h1, h401, h404, h410, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h401, h403, h409, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · linarith only [h1, h401, h404, h408, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h1, h402, h405, h407, hc23, hlam, hphi, ht12, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
            · linarith only [h1, h416, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
              · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h401, h404, h419, h421, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h401, hc01, hlam, hphi, ht0b, ht45, ht5b, p423_1, u4ehi2]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hc01, hlam, hphi, p423_1, u0ehi2]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hc01, hlam, hphi, p423_1, u0ehi3]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h404, hc01, hlam, hphi, p423_1, u0ehi3]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hc02, hlam, hphi, p423_1, u0ehi0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht12, p423_1, u0ehi3]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht12, p423_1, u0ehi4]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h0, hlam, p423_1]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, h401, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p423_1, u4ehi2]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht12, p423_1, u0ehi3]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht12, p423_1, u0ehi4]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h404, hc45, hlam, hphi, ht12, ht23, ht34, p423_1, u1ehi0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h401, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h402, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h404, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hc05, hlam, hphi, p423_1, u0ehi0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h401, h403, h419, hc03, hlam, hphi, ht0b, ht45, ht5b, p423_1, u4ehi3]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h403, hlam, p423_0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [h404, hc45, hlam, hphi, p423_1, u4ehi0]
                      · have p423_0 := h423c.1
                        have p423_1 := h423c.2.1
                        have p423_2 := h423c.2.2.1
                        have p423_3 := h423c.2.2.2
                        linarith only [hlam, p423_0]
                  · linarith only [h1, h401, h419, h420, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · linarith only [h1, h401, h418, h419, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h1, h402, h418, hc23, hlam, hphi, ht12, u1ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h452 | h452
          · linarith only [h1, h401, h403, h452, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
            · linarith only [h1, h454, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
              · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
                  · linarith only [h1, h401, h403, h457, h458, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h401, h457, h458, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · linarith only [h1, h401, h456, h457, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h402, h403, h456, hc13, hc35, hlam, hphi]
      · linarith only [h1, h401, h402, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h464 | h464
      · rcases m.htr 0 3 5 (by decide) (by decide) with h465 | h465
        · rcases m.htr 0 4 5 (by decide) (by decide) with h466 | h466
          · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
            · linarith only [h1, h467, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
              · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                · rcases m.htr 2 3 5 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                    · linarith only [h0, h469, h472, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases h0bigk with h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c | h474c
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hc01, hlam, hphi, p474_1, u0ehi1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h464, h466, h472, hc01, hlam, hphi, ht0b, ht45, ht5b, p474_1, u4ehi3]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h466, h472, hc01, hlam, hphi, ht0b, ht45, ht5b, p474_1, u4ehi3]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hc01, hlam, hphi, p474_1, u0ehi4]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hc02, hlam, hphi, p474_1, u0ehi0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h1, hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h401, hlam, p474_1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h466, h472, hc02, hlam, hphi, ht0b, ht45, ht5b, p474_1, u4ehi3]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h0, hlam, p474_1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, p474_1, u0ehi1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h1, h466, h472, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p474_1, u4ehi3]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h1, h466, h472, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p474_1, u4ehi3]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hc04, hlam, hphi, p474_1, u0ehi0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h401, h470, hc23, hlam, hphi, ht01, ht12, p474_1, u0ehi1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h464, hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h401, h466, h470, h472, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p474_1, u4ehi3]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hc05, hlam, hphi, p474_1, u0ehi0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h0, h464, h466, hc01, hlam, hphi, p474_1, u0ehi1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h465, hlam, p474_0]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [h466, hlam, p474_1]
                      · have p474_0 := h474c.1
                        have p474_1 := h474c.2.1
                        have p474_2 := h474c.2.2.1
                        have p474_3 := h474c.2.2.2
                        linarith only [hlam, p474_0]
                  · linarith only [h1, h471, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h1, h469, h470, hc13, hlam, hphi, ht01, u0ehi2]
              · linarith only [h1, h464, h469, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
            · linarith only [h1, h503, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
              · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h508 | h508
                    · linarith only [h0, h466, h505, h508, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hc01, hlam, hphi, p510_1, u0ehi1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hc01, hlam, hphi, p510_1, u0ehi2]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hc01, hlam, hphi, p510_1, u0ehi3]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h401, h466, hc01, hlam, hphi, p510_1, u0ehi1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h401, hc24, hlam, hphi, ht12, p510_1, u1ehi0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h1, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h401, hlam, p510_1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h401, h466, hlam, p510_1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h0, hlam, p510_1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hc03, hlam, hphi, p510_1, u0ehi1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht12, p510_1, u0ehi3]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht12, p510_1, u0ehi4]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hc04, hlam, hphi, p510_1, u0ehi0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h1, h464, hc23, hlam, hphi, ht01, ht12, p510_1, u0ehi1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h464, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h466, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hc05, hlam, hphi, p510_1, u0ehi0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h466, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p510_1, u0ehi1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h465, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h466, hc45, hlam, hphi, p510_1, u4ehi0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                  · linarith only [h1, h507, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h1, h505, h506, hc13, hlam, hphi, ht01, u0ehi2]
              · linarith only [h1, h464, h505, hc23, hlam, hphi, ht12, u1ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h539 | h539
          · linarith only [h464, h465, h539, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
            · linarith only [h1, h541, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
              · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
                  · linarith only [h0, h465, h543, h545, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h545, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h0, h1, h543, h544, hc03, hlam, hphi, u0ehi1]
              · linarith only [h464, h465, h543, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h550 | h550
        · rcases m.htr 0 4 5 (by decide) (by decide) with h551 | h551
          · rcases m.htr 1 2 3 (by decide) (by decide) with h552 | h552
            · linarith only [h1, h552, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
              · linarith only [h464, h550, h554, hc13, hlam, hphi, ht01, u0ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                · linarith only [h464, h550, h556, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                · linarith only [h1, h556, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · linarith only [h464, h550, h551, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
          · rcases m.htr 1 2 3 (by decide) (by decide) with h561 | h561
            · linarith only [h1, h561, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h563 | h563
              · linarith only [h0, h464, h563, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                · linarith only [h464, h565, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · linarith only [h1, h565, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
            · linarith only [h1, h568, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
              · linarith only [h0, h464, h570, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
                · linarith only [h1, h464, h572, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                · linarith only [h1, h572, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

end R2N4
