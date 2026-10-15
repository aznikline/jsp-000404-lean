import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_24_L_0_H_I_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                  · rcases h4bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h9, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h6, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h8, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo3]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h9, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h5, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
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
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h3, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, h3, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h2, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h5, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h7, h9, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h9, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h3, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h6, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h8, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h8, h9, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, h7, hlam, p36_1]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h7, hlam, p36_0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, h3, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [h1, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p36_1, u3elo0]
                    · have p36_0 := h36c.1
                      have p36_1 := h36c.2.1
                      have p36_2 := h36c.2.2.1
                      have p36_3 := h36c.2.2.2
                      linarith only [hlam, p36_0]
                · linarith only [h3, h8, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                  · linarith only [h5, h64, h7, hlam]
                  · rcases h4bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h3, h63, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h3, h5, h63, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h1, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h63, h7, hc34, hc45, hlam, hphi, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h7, hc34, hc45, hlam, hphi, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h7, hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h2, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h5, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h64, hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h3, hlam, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h6, hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h63, hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo3]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h5, h63, hc34, hc45, hlam, hphi, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [h63, hc34, hc45, hlam, hphi, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p66_1]
                    · have p66_0 := h66c.1
                      have p66_1 := h66c.2.1
                      have p66_2 := h66c.2.2.1
                      have p66_3 := h66c.2.2.2
                      linarith only [hlam, p66_0]
                · linarith only [h3, h63, hc23, hlam, hphi, u3elo0]
            · linarith only [h3, h6, hc13, hlam, hphi, u3elo0]
          · linarith only [h2, h3, h4, h5, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
          · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
            · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
              · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                  · linarith only [h4, h95, h99, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h4, h95, h97, h99, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h4, h98, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h4, h95, h97, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases h4bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h103, h3, h95, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p106_1, u3elo0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h103, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p106_1, u3elo0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p106_1, u3elo0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h103, h3, h95, h97, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p106_1, u3elo0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h1, hlam, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h103, h97, hc34, hc45, hlam, hphi, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h4, h95, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p106_1, u3elo2]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h97, hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h2, hlam, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h95, hlam, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h104, hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h3, hlam, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h96, hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h103, hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hlam, p106_0]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h104, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p106_1, u3elo3]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hc14, hc45, hlam, hphi, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [h103, hc34, hc45, hlam, hphi, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p106_1]
                    · have p106_0 := h106c.1
                      have p106_1 := h106c.2.1
                      have p106_2 := h106c.2.2.1
                      have p106_3 := h106c.2.2.2
                      linarith only [hlam, p106_0]
                · linarith only [h103, h4, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h3, h96, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
            · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
              · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                  · rcases h4bigk with h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h3, h95, hc12, hlam, hphi, ht23, p138_1, u3elo0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h3, h95, hc12, hlam, hphi, ht23, p138_1, u3elo0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p138_1, u3elo0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p138_1, u3elo0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h1, hlam, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h95, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h134, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p138_1, u3elo1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h2, hlam, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h136, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p138_1, u3elo2]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p138_1, u3elo0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p138_1, u3elo0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h3, hlam, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h134, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h136, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h134, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h135, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h135, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h137, hlam, p138_0]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [h135, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p138_1]
                    · have p138_0 := h138c.1
                      have p138_1 := h138c.2.1
                      have p138_2 := h138c.2.2.1
                      have p138_3 := h138c.2.2.2
                      linarith only [hlam, p138_0]
                  · linarith only [h135, h137, h95, hlam]
                · linarith only [h136, h3, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                  · linarith only [h135, h167, h2, h3, h95, hc12, hlam, hphi, ht23, u3elo0]
                  · rcases h4bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h3, h95, hc12, hlam, hphi, ht23, p169_1, u3elo0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p169_1, u3elo0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p169_1, u3elo0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h167, h3, h95, hc12, hlam, hphi, ht23, p169_1, u3elo0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h1, hlam, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h95, hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h135, hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h2, hlam, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h167, hc14, hc45, hlam, hphi, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h167, hc34, hc45, hlam, hphi, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h167, hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h3, hlam, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h134, hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h166, hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hlam, p169_0]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h167, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p169_1, u3elo3]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h95, hc12, hc45, hlam, hphi, ht23, ht34, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [h95, hc12, hc45, hlam, hphi, ht23, ht34, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p169_1]
                    · have p169_0 := h169c.1
                      have p169_1 := h169c.2.1
                      have p169_2 := h169c.2.2.1
                      have p169_3 := h169c.2.2.2
                      linarith only [hlam, p169_0]
                · linarith only [h166, h3, h4, hc13, hlam, hphi, u3elo0]
            · linarith only [h134, h3, h4, hc12, hlam, hphi, ht23, u3elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
        · rcases m.htr 1 2 4 (by decide) (by decide) with h198 | h198
          · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
            · linarith only [h0, h199, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                · linarith only [h0, h197, h202, h3, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                  · rcases h4bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h198, h204, hc04, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h1, h204, hc01, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h3, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo3]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h1, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h204, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h199, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h1, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo3]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h2, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h198, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h202, hlam, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p205_1, u3elo3]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p205_1, u3elo3]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p205_1, u3elo3]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p205_1, u3elo3]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h198, h204, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h201, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h204, hlam, p205_0]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [h198, h204, h3, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p205_1]
                    · have p205_0 := h205c.1
                      have p205_1 := h205c.2.1
                      have p205_2 := h205c.2.2.1
                      have p205_3 := h205c.2.2.2
                      linarith only [hlam, p205_0]
                  · linarith only [h1, h201, h202, h204, h3, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                · linarith only [h0, h197, h232, h3, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                  · linarith only [h199, h2, h201, h234, h3, hc13, hlam, hphi, u3elo3]
                  · rcases h4bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h197, h199, h3, hc23, hlam, hphi, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h3, hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h197, h199, h201, h3, hc23, hlam, hphi, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h1, hlam, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h201, h232, hc23, hc45, hlam, hphi, ht34, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h199, hlam, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h201, hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h2, hlam, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h198, hlam, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h232, hlam, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h234, hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h232, hc23, hlam, hphi, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hlam, p236_0]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h201, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p236_1, u3elo3]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h0, h197, h3, hc23, hc45, hlam, hphi, ht34, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h198, h232, hc23, hc45, hlam, hphi, ht34, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [h232, hc23, hc45, hlam, hphi, ht34, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p236_1]
                    · have p236_0 := h236c.1
                      have p236_1 := h236c.2.1
                      have p236_2 := h236c.2.2.1
                      have p236_3 := h236c.2.2.2
                      linarith only [hlam, p236_0]
          · linarith only [h197, h198, h2, h3, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
          · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
            · linarith only [h0, h264, h3, hlam]
            · linarith only [h197, h263, h264, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h267 | h267
            · linarith only [h0, h267, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
              · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                · linarith only [h270, h3, hc03, hlam, hphi, u3elo2]
                · linarith only [h197, h270, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
                · linarith only [h0, h197, h273, h3, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h197, h273, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
      · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
        · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
          · linarith only [h1, h2, h278, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
            · linarith only [h277, h278, h280, hlam]
            · linarith only [h276, h280, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h283 | h283
          · linarith only [h2, h277, h283, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h285 | h285
            · rcases m.htr 1 4 5 (by decide) (by decide) with h286 | h286
              · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                · rcases m.htr 2 4 5 (by decide) (by decide) with h288 | h288
                  · rcases h4bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h286, hc04, hc45, hlam, hphi, ht0b, ht5b, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h2, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h276, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p289_1, u3elo0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h2, h287, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, hlam, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h283, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, h2, h287, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h287, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p289_1, u3elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h287, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p289_1, u3elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h287, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p289_1, u3elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h287, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo2]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h276, hlam, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h285, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h287, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo3]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, h286, hlam, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h286, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h288, hlam, p289_0]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [h1, h286, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p289_1]
                    · have p289_0 := h289c.1
                      have p289_1 := h289c.2.1
                      have p289_2 := h289c.2.2.1
                      have p289_3 := h289c.2.2.2
                      linarith only [hlam, p289_0]
                  · linarith only [h1, h2, h286, h288, hlam]
                · linarith only [h276, h287, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                  · linarith only [h283, h286, h317, h318, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases h4bigk with h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, h283, h317, hc12, hlam, hphi, ht23, p320_1, u3elo2]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, h318, hc34, hc45, hlam, hphi, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, h318, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h1, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h283, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h286, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h318, hc04, hc45, hlam, hphi, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h318, hc14, hc45, hlam, hphi, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h318, hc34, hc45, hlam, hphi, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h318, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h276, hlam, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h285, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h317, hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, h318, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p320_1, u3elo3]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h1, h283, hc12, hc45, hlam, hphi, ht23, ht34, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h283, hc12, hc45, hlam, hphi, ht23, ht34, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [h2, hc02, hc45, hlam, hphi, ht23, ht34, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p320_1]
                    · have p320_0 := h320c.1
                      have p320_1 := h320c.2.1
                      have p320_2 := h320c.2.2.1
                      have p320_3 := h320c.2.2.2
                      linarith only [hlam, p320_0]
                · linarith only [h276, h317, hc23, hlam, hphi, u3elo0]
            · linarith only [h276, h285, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h348 | h348
        · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
          · linarith only [h1, h2, h349, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
            · linarith only [h276, h351, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h353 | h353
              · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                · linarith only [h0, h276, h348, h354, hlam]
                · linarith only [h348, h349, h354, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                · linarith only [h0, h276, h348, h349, h357, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h348, h349, h357, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h360 | h360
          · linarith only [h2, h348, h360, hc02, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
            · linarith only [h0, h276, h362, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
              · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                · linarith only [h276, h365, hc03, hlam, hphi, u3elo2]
                · linarith only [h348, h365, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                · linarith only [h0, h276, h348, h368, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h348, h368, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h371 | h371
    · rcases m.htr 0 3 4 (by decide) (by decide) with h372 | h372
      · linarith only [h0, h1, h372, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h374 | h374
        · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
          · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
            · linarith only [h372, h376, hc03, hlam, hphi, u3elo1]
            · linarith only [h0, h1, h376, hc13, hlam, hphi, u3elo3]
          · linarith only [h371, h372, h374, h375, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
          · linarith only [h0, h1, h374, h380, hlam]
          · linarith only [h0, h1, h371, h372, h374, h380, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h383 | h383
      · linarith only [h0, h1, h383, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
        · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
          · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
            · linarith only [h383, h387, hc03, hlam, hphi, u3elo1]
            · linarith only [h0, h1, h387, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
            · linarith only [h0, h1, h383, h390, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h1, h385, h390, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
          · linarith only [h0, h1, h371, h385, h393, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
            · linarith only [h0, h1, h383, h395, hlam]
            · linarith only [h0, h1, h385, h395, hc12, hlam, hphi, ht23, u3elo3]

end R2N4
