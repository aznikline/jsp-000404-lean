import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                  · rcases h5bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, h4, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u0elo2, u3ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, h4, hc25, hlam, hphi, ht0b, ht5b, p10_1, u0elo2]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u0elo2, u3ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, h4, hc45, hlam, hphi, ht0b, ht5b, p10_1, u0elo2]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10_1, u3ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1, u0elo0, u3ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p10_1, u0elo1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10_1, u3ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p10_1, u0elo1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h5, hc45, hlam, hphi, ht0b, ht5b, p10_1, u0elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h4, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hc45, hlam, hphi, ht34, p10_1, u3ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h8, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h9, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                  · linarith only [h2, h4, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                · linarith only [h2, h4, h6, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
              · linarith only [h0, h5, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h2, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h3, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
          · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
            · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                · linarith only [h1, h2, h4, h44, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                  · linarith only [h2, h4, h46, hlam]
                  · rcases h5bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hc15, hlam, hphi, ht0b, ht5b, p48_1, u0elo4]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p48_1, u0elo0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u0elo0, u3ehi4]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h4, hlam, p48_1]
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
                      linarith only [h42, h44, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h0, h46, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u0elo0, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h0, h4, hc04, hlam, hphi, ht0b, ht45, ht5b, p48_1, u0elo0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, h41, h46, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u0elo4, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h1, h46, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u0elo1, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h44, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h3, hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h41, hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h43, hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h46, hlam, p48_1]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h0, h41, h46, hc45, hlam, hphi, ht34, p48_1, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h41, h46, hc45, hlam, hphi, ht34, p48_1, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h43, h46, hc45, hlam, hphi, ht34, p48_1, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [h46, hc45, hlam, hphi, ht34, p48_1, u3ehi3]
                    · have p48_0 := h48c.1
                      have p48_1 := h48c.2.1
                      have p48_2 := h48c.2.2.1
                      have p48_3 := h48c.2.2.2
                      linarith only [hlam, p48_0]
              · linarith only [h0, h41, h43, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h2, h42, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h3, h41, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
      · linarith only [h2, h3, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h78 | h78
      · linarith only [h2, h78, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
        · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
          · linarith only [h0, h78, h81, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
            · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
              · linarith only [h1, h81, h84, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
              · linarith only [h83, h84, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
              · linarith only [h78, h83, h87, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
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
                      linarith only [h80, h81, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u0elo3, u3ehi1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h80, hc25, hlam, hphi, ht0b, ht5b, p91_1, u0elo3]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h78, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hc45, hlam, hphi, ht0b, ht5b, p91_1, u0elo4]
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
                      linarith only [h87, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p91_1, u3ehi2]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h81, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p91_1, u0elo0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h1, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p91_1, u0elo1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h87, hlam, p91_1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p91_1, u0elo1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h0, h81, hc35, hlam, hphi, p91_1, u3ehi1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h81, hc35, hlam, hphi, p91_1, u3ehi1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h87, hc35, hlam, hphi, p91_1, u3ehi2]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      rcases p91_3 (m.d 0 5) (by simp) with h111 | h111
                      · linarith only [h111, h78, hlam]
                      · linarith only [h111, h80, hlam]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h80, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h81, hc45, hlam, hphi, ht34, p91_1, u3ehi1]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h89, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [h90, hlam, p91_0]
                    · have p91_0 := h91c.1
                      have p91_1 := h91c.2.1
                      have p91_2 := h91c.2.2.1
                      have p91_3 := h91c.2.2.2
                      linarith only [hlam, p91_0]
                  · linarith only [h1, h89, h90, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h80, h83, h89, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
          · linarith only [h0, h121, h78, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
            · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h1, h124, h78, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
              · linarith only [h123, h124, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
              · linarith only [h123, h127, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                · linarith only [h123, h129, h2, h80, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                  · linarith only [h131, h2, h80, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h131, h2, hc45, hlam, hphi, ht34, u3ehi0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h134 | h134
    · rcases m.htr 0 3 5 (by decide) (by decide) with h135 | h135
      · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
        · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
          · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
              · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                  · rcases h5bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h136, hc15, hlam, hphi, ht0b, ht5b, p142_1, u0elo3]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h1, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo4, u3ehi4]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h134, h136, hc45, hlam, hphi, ht0b, ht5b, p142_1, u0elo2]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h0, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p142_1]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0, u3ehi4]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p142_1, u0elo0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h1, h138, h140, hc02, hc23, hlam, hphi, p142_1]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h137, h138, h140, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p142_1, u3ehi4]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h138, h140, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p142_1, u3ehi4]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      rcases p142_3 (m.d 0 5) (by simp) with h157 | h157
                      · linarith only [h1, h157, hlam]
                      · linarith only [h136, h157, hlam]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h135, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h137, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h139, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h0, h137, hc45, hlam, hphi, ht0b, ht5b, p142_1, u0elo4]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h136, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h137, hc45, hlam, hphi, ht34, p142_1, u3ehi4]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h140, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [h141, hlam, p142_0]
                    · have p142_0 := h142c.1
                      have p142_1 := h142c.2.1
                      have p142_2 := h142c.2.2.1
                      have p142_3 := h142c.2.2.2
                      linarith only [hlam, p142_0]
                  · linarith only [h134, h136, h141, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                · linarith only [h134, h136, h138, h140, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
              · linarith only [h0, h137, h139, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h134, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h135, h137, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
          · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
            · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
              · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                · rcases m.htr 3 4 5 (by decide) (by decide) with h179 | h179
                  · linarith only [h134, h136, h179, hlam]
                  · rcases h5bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h136, h176, h178, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p181_1]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h1, hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h136, h176, h178, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p181_1, u3ehi4]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h136, hlam, p181_1]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h0, hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p181_1, u0elo0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h0, h179, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u0elo0, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h0, h136, hc04, hlam, hphi, ht0b, ht45, ht5b, p181_1, u0elo0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h1, hc02, hc25, hlam, hphi, p181_1]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h175, h176, h178, h179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p181_1, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h176, h178, h179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p181_1, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h134, h136, h176, h178, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p181_1, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h135, hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h175, hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h177, hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h179, hlam, p181_1]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h0, h175, h179, hc45, hlam, hphi, ht34, p181_1, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h175, h176, h178, h179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p181_1, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h178, hlam, p181_0]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [h176, h178, h179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p181_1, u3ehi3]
                    · have p181_0 := h181c.1
                      have p181_1 := h181c.2.1
                      have p181_2 := h181c.2.2.1
                      have p181_3 := h181c.2.2.2
                      linarith only [hlam, p181_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h207 | h207
                  · linarith only [h1, h134, h178, h207, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases h5bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hc15, hlam, hphi, ht0b, ht5b, p209_1, u0elo4]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h1, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u0elo0, u3ehi4]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h136, hlam, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h1, hc05, hlam, hphi, ht0b, ht5b, p209_1, u0elo0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h207, hlam, hphi, ht0b, ht34, ht45, ht5b, p209_1, u0elo4, u3ehi3]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h1, h178, hc05, hlam, hphi, ht0b, ht5b, p209_1, u0elo0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h1, h178, hc02, hc45, hlam, hphi, ht23, ht34, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h175, h178, h207, hc45, hlam, hphi, ht34, p209_1, u3ehi3]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h178, h207, hc45, hlam, hphi, ht34, p209_1, u3ehi3]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h178, hlam, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h135, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h175, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h177, hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h207, hlam, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h0, h175, h207, hc45, hlam, hphi, ht34, p209_1, u3ehi3]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h175, h207, hc45, hlam, hphi, ht34, p209_1, u3ehi3]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p209_1]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [h207, hc45, hlam, hphi, ht34, p209_1, u3ehi3]
                    · have p209_0 := h209c.1
                      have p209_1 := h209c.2.1
                      have p209_2 := h209c.2.2.1
                      have p209_3 := h209c.2.2.2
                      linarith only [hlam, p209_0]
              · linarith only [h0, h175, h177, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h134, h176, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h135, h175, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
      · linarith only [h134, h135, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h239 | h239
      · linarith only [h134, h239, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
        · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
          · linarith only [h0, h239, h242, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
            · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
              · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                  · rcases h5bigk with h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h134, h241, h244, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p248_1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h1, hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h239, hlam, p248_1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h134, h241, h244, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p248_1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h0, hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h245, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p248_1, u3ehi4]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h242, hlam, p248_1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p248_1, u0elo4]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h1, hc02, hc25, hlam, hphi, p248_1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h242, h244, h246, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p248_1, u3ehi1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h239, h244, h246, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p248_1, u3ehi0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      rcases p248_3 (m.d 0 5) (by simp) with h263 | h263
                      · linarith only [h1, h263, hlam]
                      · linarith only [h241, h263, hlam]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h0, h242, hc35, hlam, hphi, p248_1, u3ehi1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h242, hc35, hlam, hphi, p248_1, u3ehi1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h245, hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h244, h247, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p248_1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h241, hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h242, hc45, hlam, hphi, ht34, p248_1, u3ehi1]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h246, hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [h247, hlam, p248_0]
                    · have p248_0 := h248c.1
                      have p248_1 := h248c.2.1
                      have p248_2 := h248c.2.2.1
                      have p248_3 := h248c.2.2.2
                      linarith only [hlam, p248_0]
                  · linarith only [h134, h241, h247, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi0]
                · linarith only [h134, h241, h244, h246, hlam]
              · linarith only [h244, h245, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
              · linarith only [h239, h244, h279, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                  · rcases h5bigk with h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c | h283c
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h241, h242, hlam, hphi, ht0b, ht34, ht45, ht5b, p283_1, u0elo3, u3ehi1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h1, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h239, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hc45, hlam, hphi, ht0b, ht5b, p283_1, u0elo4]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h1, hc05, hlam, hphi, ht0b, ht5b, p283_1, u0elo0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h242, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p283_1, u0elo4]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h1, hc02, hc25, hlam, hphi, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h242, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p283_1, u3ehi1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h279, hlam, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 5) (by simp) with h298 | h298
                      · linarith only [h1, h298, hlam]
                      · linarith only [h241, h298, hlam]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h0, h242, h282, hc34, hlam, hphi, p283_1, u3ehi1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h242, h282, hc34, hlam, hphi, p283_1, u3ehi1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h1, h282, hc02, hc34, hlam, hphi, ht23, p283_1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      rcases p283_3 (m.d 0 5) (by simp) with h305 | h305
                      · linarith only [h239, h305, hlam]
                      · linarith only [h241, h305, hlam]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h241, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h242, hc45, hlam, hphi, ht34, p283_1, u3ehi1]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h281, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [h282, hlam, p283_0]
                    · have p283_0 := h283c.1
                      have p283_1 := h283c.2.1
                      have p283_2 := h283c.2.2.1
                      have p283_3 := h283c.2.2.2
                      linarith only [hlam, p283_0]
                  · linarith only [h134, h241, h282, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi0]
                · linarith only [h241, h244, h281, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
          · linarith only [h0, h239, h315, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
            · rcases m.htr 2 3 5 (by decide) (by decide) with h318 | h318
              · rcases m.htr 2 4 5 (by decide) (by decide) with h319 | h319
                · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                  · linarith only [h134, h241, h317, h320, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h134, h320, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h134, h317, h319, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h134, h317, h318, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
              · linarith only [h317, h325, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                · linarith only [h134, h241, h317, h327, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                  · linarith only [h134, h241, h329, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h134, h329, hc45, hlam, hphi, ht34, u3ehi0]

end R2N4
