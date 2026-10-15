import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                    · rcases h5bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h1, hlam, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h4, hlam, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p12_1, u2elo4]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h6, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h9, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo4]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h3, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h7, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h11, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                    · rcases h5bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p38_1, u3elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p38_1, u3elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p38_1, u3elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h11, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p38_1, u3elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h0, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p38_1]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p38_1, u3elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h0, h11, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p38_1, u3elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h1, hlam, p38_1]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h4, hlam, p38_1]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p38_1, u2elo4]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h1, h11, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38_1, u2elo0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h2, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h6, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h9, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h11, hlam, p38_1]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h3, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h7, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h10, hlam, p38_0]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [h3, hc04, hc35, hlam, hphi, ht0b, ht5b, p38_1]
                      · have p38_0 := h38c.1
                        have p38_1 := h38c.2.1
                        have p38_2 := h38c.2.2.1
                        have p38_3 := h38c.2.2.2
                        linarith only [hlam, p38_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h10, h5, h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
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
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h2, h64, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h10, h2, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h2, h64, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h10, h2, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h1, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h4, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h64, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p66_1, u2elo4]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h10, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h2, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h6, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h9, hlam, p66_0]
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
                        linarith only [h3, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h7, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h3, hc04, hc25, hlam, hphi, ht0b, ht5b, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h5, h64, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                · linarith only [h2, h9, hc23, hlam, hphi, u3elo0]
              · linarith only [h5, h8, hc23, hlam, hphi, u3elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
              · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h4, h7, h96, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                    · linarith only [h5, h96, h98, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · rcases h5bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, h95, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h0, hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h0, h95, hc01, hc35, hlam, hphi, ht0b, ht5b, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h7, hlam, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h1, hlam, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h4, hlam, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p100_1, u2elo4]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h96, hlam, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h6, hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h95, hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h98, hlam, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h3, hlam, p100_0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h3, hc04, hc15, hlam, hphi, ht0b, ht5b, p100_1]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p100_1, u3elo0]
                      · have p100_0 := h100c.1
                        have p100_1 := h100c.2.1
                        have p100_2 := h100c.2.2.1
                        have p100_3 := h100c.2.2.2
                        linarith only [hlam, p100_0]
                · linarith only [h2, h95, hc23, hlam, hphi, u3elo0]
              · linarith only [h5, h94, hc23, hlam, hphi, u3elo1]
          · linarith only [h2, h6, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
          · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
            · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
              · linarith only [h129, h131, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                    · rcases h5bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h135, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h0, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p136_1]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h129, h135, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo3]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h129, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo3]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h1, hlam, p136_1]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h4, hlam, p136_1]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h135, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p136_1, u2elo4]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h129, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo3]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h2, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h129, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h133, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p136_1, u3elo4]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h3, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h130, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h134, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [h135, hlam, p136_0]
                      · have p136_0 := h136c.1
                        have p136_1 := h136c.2.1
                        have p136_2 := h136c.2.2.1
                        have p136_3 := h136c.2.2.2
                        linarith only [hlam, p136_0]
                    · linarith only [h129, h135, h3, h5, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h129, h130, h131, h134, h5, hc23, hlam, hphi, u3elo3]
                · linarith only [h133, h2, hc23, hlam, hphi, u3elo0]
            · linarith only [h129, h130, h5, hlam]
          · linarith only [h129, h2, hc13, hlam, hphi, u3elo0]
      · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
      · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
        · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
          · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
            · linarith only [h0, h171, h3, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
              · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
                  · linarith only [h0, h168, h175, h3, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                    · linarith only [h169, h171, h177, hlam]
                    · rcases h5bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h1, h168, h174, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p179_1, u2elo0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h1, h174, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p179_1, u2elo0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p179_1, u3elo0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h3, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h174, hc01, hc35, hlam, hphi, ht0b, ht5b, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p179_1, u3elo0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h171, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h1, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h168, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p179_1, u2elo4]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h175, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h2, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h170, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h174, hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h177, hlam, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h3, hc04, hc45, hlam, hphi, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h171, hc14, hc45, hlam, hphi, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h175, hc24, hc45, hlam, hphi, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [h177, hc34, hc45, hlam, hphi, p179_1]
                      · have p179_0 := h179c.1
                        have p179_1 := h179c.2.1
                        have p179_2 := h179c.2.2.1
                        have p179_3 := h179c.2.2.2
                        linarith only [hlam, p179_0]
                · linarith only [h174, h2, hc23, hlam, hphi, u3elo0]
              · linarith only [h169, h173, hc23, hlam, hphi, u3elo1]
          · linarith only [h170, h2, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
          · rcases m.htr 1 4 5 (by decide) (by decide) with h209 | h209
            · linarith only [h0, h209, h3, hlam]
            · linarith only [h169, h208, h209, hlam]
          · linarith only [h2, h208, hc13, hlam, hphi, u3elo0]
      · linarith only [h1, h168, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h214 | h214
    · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
      · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
        · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
          · linarith only [h2, h217, hc03, hlam, hphi, u3elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
            · linarith only [h216, h217, h219, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
              · rcases m.htr 2 3 5 (by decide) (by decide) with h222 | h222
                · linarith only [h217, h222, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                  · linarith only [h215, h219, h221, h222, h224, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                    · linarith only [h215, h219, h221, h222, h226, hlam]
                    · linarith only [h2, h214, h226, hlam]
              · linarith only [h216, h221, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
          · linarith only [h2, h216, h230, hc03, hlam, hphi, u3elo3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
            · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
              · linarith only [h216, h233, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                · linarith only [h2, h233, h235, hc03, hlam, hphi, u3elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                    · rcases h5bigk with h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h2, h215, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h2, h237, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h2, hlam, p239_1]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h0, hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h0, h237, hc01, hc45, hlam, hphi, ht0b, ht5b, p239_1]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h230, hlam, p239_1]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h1, hlam, p239_1]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h215, hlam, p239_1]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h235, hlam, p239_1]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p239_1, u2elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo4]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h238, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p239_1, u3elo3]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h214, hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h232, hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h237, hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [h238, hlam, p239_0]
                      · have p239_0 := h239c.1
                        have p239_1 := h239c.2.1
                        have p239_2 := h239c.2.2.1
                        have p239_3 := h239c.2.2.2
                        linarith only [hlam, p239_0]
                    · linarith only [h216, h237, h238, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h216, h232, h233, h237, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
              · linarith only [h216, h267, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                · linarith only [h2, h214, h232, h267, h269, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                  · linarith only [h216, h232, h267, h271, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                    · linarith only [h216, h232, h273, hc13, hlam, hphi, u3elo3]
                    · linarith only [h2, h214, h216, h273, hc13, hlam, hphi, u3elo4]
      · linarith only [h1, h215, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
      · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
        · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
          · linarith only [h2, h279, hc03, hlam, hphi, u3elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
            · linarith only [h214, h278, h279, h281, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
              · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                · linarith only [h2, h284, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h286 | h286
                  · linarith only [h281, h283, h284, h286, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h0, h214, h277, h283, h284, h288, hlam]
                    · rcases h5bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h277, h283, h284, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h1, h283, h284, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p290_1, u2elo0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h2, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h214, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h283, h284, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h279, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h281, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h1, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h277, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h284, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h286, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p290_1, u3elo4]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h277, h283, h284, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p290_1, u3elo4]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h283, h284, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p290_1, u3elo4]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h288, hlam, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h0, h277, h283, h284, hc34, hc45, hlam, hphi, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h277, h283, h284, hc34, hc45, hlam, hphi, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h283, h284, hc34, hc45, hlam, hphi, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [h2, hc03, hc45, hlam, hphi, ht34, p290_1]
                      · have p290_0 := h290c.1
                        have p290_1 := h290c.2.1
                        have p290_2 := h290c.2.2.1
                        have p290_3 := h290c.2.2.2
                        linarith only [hlam, p290_0]
              · linarith only [h278, h279, h283, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h317 | h317
          · linarith only [h2, h278, h317, hc03, hlam, hphi, u3elo3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
            · linarith only [h0, h214, h319, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
              · linarith only [h278, h321, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                · linarith only [h2, h321, h323, hc03, hlam, hphi, u3elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                  · linarith only [h278, h319, h321, h325, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
                    · linarith only [h278, h319, h327, hc13, hlam, hphi, u3elo3]
                    · rcases h5bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [hlam, p329_0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p329_1, u2elo0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h1, h325, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p329_1, u2elo0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h2, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h214, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h0, hlam, p329_0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [hlam, p329_0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h0, h325, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h317, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h319, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h1, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h277, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [hlam, p329_0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h323, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h325, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p329_1, u3elo4]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h277, h325, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p329_1, u3elo4]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h321, h325, hc23, hlam, hphi, p329_1, u3elo4]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [hlam, p329_0]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h327, hlam, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h0, h277, h321, h325, hc23, hc45, hlam, hphi, ht34, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h277, h321, h325, hc23, hc45, hlam, hphi, ht34, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h321, h325, hc23, hc45, hlam, hphi, ht34, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [h2, hc03, hc45, hlam, hphi, ht34, p329_1]
                      · have p329_0 := h329c.1
                        have p329_1 := h329c.2.1
                        have p329_2 := h329c.2.2.1
                        have p329_3 := h329c.2.2.2
                        linarith only [hlam, p329_0]
      · linarith only [h1, h277, hc12, hlam, hphi, u2elo0]

end R2N4
