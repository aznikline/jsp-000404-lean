import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S2
import Jsp000404.R1LeavesN7_51S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1471 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2025 | h2025
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2026 | h2026
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2027 | h2027
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2028 | h2028
        · linarith only [h1471, h2028, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2030 | h2030
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2031 | h2031
            · linarith only [h0, h2027, h2028, h2031, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h0, h2025, h2031, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2034 | h2034
            · linarith only [h0, h2027, h2028, h2034, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h0, h2025, h2034, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2037 | h2037
        · linarith only [h1471, h2027, h2037, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2039 | h2039
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2040 | h2040
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2041 | h2041
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2042 | h2042
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2043 | h2043
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2044 | h2044
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2045 | h2045
                      · rcases h5bigk with h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c | h2046c
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h0, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1471, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1471, h2042, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo2]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h1471, h2042, h2044, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo2]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h0, h2039, h2041, hc01, hc13, hlam, hphi, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2037, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2037, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo3]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2027, h2039, h2041, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo2]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h0, h2044, hc01, hlam, hphi, ht12, p2046_1, u2elo3]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2044, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo3]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2042, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo2]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2042, h2044, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2046_1, u2elo2]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2025, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2040, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2043, hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2025, hc03, hc45, hlam, hphi, ht0b, ht5b, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2026, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2041, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2044, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [h2045, hlam, p2046_1]
                        · have p2046_0 := h2046c.1
                          have p2046_1 := h2046c.2.1
                          have p2046_2 := h2046c.2.2.1
                          have p2046_3 := h2046c.2.2.2
                          linarith only [hlam, p2046_0]
                      · rcases h5bigk with h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h0, hlam, p2072_1]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h1471, hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h0, h2037, h2042, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h0, h2037, h2042, h2044, h2045, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2037, h2042, h2044, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2037, hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2037, h2042, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2037, h2042, h2044, h2045, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2026, h2042, h2044, h2045, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2042, h2044, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2042, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2042, h2044, h2045, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2025, hlam, p2072_1]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2040, hlam, p2072_1]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2043, hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2045, hlam, p2072_0]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2026, hlam, p2072_1]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2041, hlam, p2072_1]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h2044, hlam, p2072_1]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [h1471, h2026, h2042, h2044, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2072_1, u2elo2]
                        · have p2072_0 := h2072c.1
                          have p2072_1 := h2072c.2.1
                          have p2072_2 := h2072c.2.2.1
                          have p2072_3 := h2072c.2.2.2
                          linarith only [hlam, p2072_0]
                    · linarith only [h1471, h2027, h2039, h2041, h2044, hc02, hlam, hphi, u2elo2]
                  · linarith only [h0, h2025, h2027, h2039, h2041, h2043, hlam]
                · linarith only [h2027, h2039, h2042, hlam]
              · linarith only [h0, h2026, h2041, hlam]
            · linarith only [h0, h2025, h2040, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2103 | h2103
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2104 | h2104
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2105 | h2105
                · linarith only [h2039, h2103, h2105, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2107 | h2107
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2108 | h2108
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2109 | h2109
                      · rcases h5bigk with h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c | h2110c
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h0, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h1471, hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h0, h2027, h2103, h2109, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo2]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h0, h2027, h2103, h2105, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2027, h2103, h2105, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2037, hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2027, h2103, h2105, h2109, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2027, h2103, h2105, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h0, h2105, h2107, hc01, hlam, hphi, ht12, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2105, h2107, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2105, h2107, h2109, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2105, h2107, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2110_1, u2elo3]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2025, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2103, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2107, hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [hlam, p2110_0]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2025, hc03, hc45, hlam, hphi, ht0b, ht5b, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2026, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2104, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2108, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [h2109, hlam, p2110_1]
                        · have p2110_0 := h2110c.1
                          have p2110_1 := h2110c.2.1
                          have p2110_2 := h2110c.2.2.1
                          have p2110_3 := h2110c.2.2.2
                          linarith only [hlam, p2110_0]
                      · linarith only [h0, h2037, h2105, h2107, h2109, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h2026, h2037, h2105, h2107, h2108, hlam]
                  · linarith only [h2027, h2103, h2107, hlam]
              · linarith only [h0, h2026, h2039, h2103, h2104, hlam]
            · linarith only [h0, h2025, h2103, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2141 | h2141
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2142 | h2142
        · linarith only [h1471, h2142, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2144 | h2144
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2145 | h2145
            · linarith only [h0, h2141, h2142, h2145, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h0, h2025, h2145, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2148 | h2148
            · linarith only [h0, h2141, h2142, h2148, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h0, h2025, h2148, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2151 | h2151
        · linarith only [h1471, h2141, h2151, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2153 | h2153
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2154 | h2154
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2155 | h2155
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2156 | h2156
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2157 | h2157
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2158 | h2158
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2159 | h2159
                      · linarith only [h0, h2026, h2141, h2153, h2159, hc01, hlam, hphi, ht12, u2elo2]
                      · rcases h5bigk with h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c | h2161c
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h0, hlam, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h1471, hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h1471, h2156, h2158, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2026, hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2151, hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2151, h2156, h2158, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2026, h2151, h2156, h2158, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h0, h2156, h2158, hc01, hlam, hphi, ht12, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2156, h2158, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2156, h2158, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2026, h2156, h2158, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2025, hlam, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2154, hlam, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2157, hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2159, hlam, p2161_0]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2155, hlam, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2158, hlam, p2161_1]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [h2141, h2153, h2155, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2161_1, u2elo2]
                        · have p2161_0 := h2161c.1
                          have p2161_1 := h2161c.2.1
                          have p2161_2 := h2161c.2.2.1
                          have p2161_3 := h2161c.2.2.2
                          linarith only [hlam, p2161_0]
                    · linarith only [h2141, h2151, h2153, h2155, h2158, hc12, hlam, hphi, u2elo2]
                  · linarith only [h2025, h2026, h2141, h2153, h2155, h2157, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h2141, h2153, h2156, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2190 | h2190
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2191 | h2191
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2192 | h2192
                    · linarith only [h0, h2155, h2192, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2194 | h2194
                      · linarith only [h2026, h2141, h2153, h2194, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases h5bigk with h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c | h2196c
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h0, hlam, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h1471, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h0, h2151, h2194, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2196_1, u2elo4]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2026, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2151, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2196_1, u2elo4]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2151, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2141, h2154, h2194, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2196_1, u2elo2]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2155, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p2196_1, u2elo4]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2196_1, u2elo4]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2191, h2194, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2196_1, u2elo2]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2192, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2025, hlam, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2154, hlam, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2191, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2194, hlam, p2196_0]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h1471, hc02, hc45, hlam, hphi, ht23, ht34, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [h2194, hc34, hc45, hlam, hphi, p2196_1]
                        · have p2196_0 := h2196c.1
                          have p2196_1 := h2196c.2.1
                          have p2196_2 := h2196c.2.2.1
                          have p2196_3 := h2196c.2.2.2
                          linarith only [hlam, p2196_0]
                  · linarith only [h0, h2025, h2141, h2151, h2191, hc12, hlam, hphi, u2elo4]
                · linarith only [h2141, h2153, h2190, hlam]
            · linarith only [h0, h2025, h2154, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2225 | h2225
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2226 | h2226
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2227 | h2227
                · linarith only [h2153, h2225, h2227, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2229 | h2229
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2230 | h2230
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2231 | h2231
                      · linarith only [h2025, h2026, h2231, hlam]
                      · linarith only [h2141, h2227, h2230, h2231, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h2141, h2151, h2226, h2227, h2230, hc12, hlam, hphi, u2elo4]
                  · linarith only [h2141, h2225, h2229, hlam]
              · linarith only [h2153, h2225, h2226, hlam]
            · linarith only [h0, h2025, h2225, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2238 | h2238
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2239 | h2239
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2240 | h2240
        · linarith only [h1471, h2240, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2242 | h2242
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2243 | h2243
            · linarith only [h2025, h2239, h2240, h2243, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2245 | h2245
              · linarith only [h0, h2239, h2240, h2242, h2245, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h2238, h2245, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2248 | h2248
            · linarith only [h2025, h2239, h2240, h2248, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2250 | h2250
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2251 | h2251
                · linarith only [h2239, h2240, h2242, h2251, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2253 | h2253
                  · linarith only [h2239, h2240, h2248, h2253, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2255 | h2255
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2256 | h2256
                      · rcases h5bigk with h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h1471, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2025, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h1471, h2255, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2257_1, u2elo3]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2250, hc01, hc14, hlam, hphi, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2240, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2248, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2240, h2255, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2257_1, u2elo3]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2255, hc01, hlam, hphi, ht12, p2257_1, u2elo3]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2255, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2257_1, u2elo3]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2253, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2255, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2257_1, u2elo3]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2239, h2240, h2255, hc01, hc23, hc35, hlam, hphi, ht12, p2257_1, u2elo3]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2239, h2240, hc23, hc35, hlam, hphi, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          rcases p2257_3 (m.d 0 5) (by simp) with h2277 | h2277
                          · linarith only [h2025, h2277, hlam]
                          · linarith only [h2238, h2277, hlam]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2238, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2250, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2255, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2256, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                      · linarith only [h2242, h2250, h2256, hlam]
                    · linarith only [h0, h2238, h2240, h2255, hlam]
              · linarith only [h0, h2238, h2250, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2288 | h2288
        · linarith only [h1471, h2239, h2288, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2290 | h2290
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2291 | h2291
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2292 | h2292
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2293 | h2293
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2294 | h2294
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2295 | h2295
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2296 | h2296
                      · rcases h5bigk with h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c | h2297c
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h0, hlam, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h1471, hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2025, hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h1471, h2293, h2295, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h0, h2292, hc01, hc14, hlam, hphi, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2288, hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2025, h2288, h2293, h2295, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2239, h2290, h2292, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h0, h2293, h2295, hc01, hlam, hphi, ht12, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2293, h2295, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2025, h2293, h2295, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2293, h2295, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h0, h2296, hc01, hc34, hlam, hphi, ht12, ht23, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2291, hlam, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2294, hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [hlam, p2297_0]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2239, h2290, h2296, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2297_1, u2elo2]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2238, hlam, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2292, hlam, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2295, hlam, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [h2296, hlam, p2297_1]
                        · have p2297_0 := h2297c.1
                          have p2297_1 := h2297c.2.1
                          have p2297_2 := h2297c.2.2.1
                          have p2297_3 := h2297c.2.2.2
                          linarith only [hlam, p2297_0]
                      · linarith only [h2025, h2238, h2296, hlam]
                    · linarith only [h1471, h2238, h2295, hlam]
                  · linarith only [h2239, h2291, h2294, hlam]
                · linarith only [h2025, h2239, h2291, h2293, hc03, hc34, hlam, hphi]
              · linarith only [h0, h2025, h2238, h2239, h2291, h2292, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2328 | h2328
              · linarith only [h2290, h2291, h2328, hlam]
              · linarith only [h0, h2238, h2328, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2331 | h2331
            · linarith only [h2025, h2290, h2331, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2333 | h2333
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2334 | h2334
                · linarith only [h2239, h2290, h2334, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2336 | h2336
                  · linarith only [h0, h2331, h2334, h2336, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2338 | h2338
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2339 | h2339
                      · rcases h5bigk with h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c | h2340c
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h0, hlam, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h1471, hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2025, hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h1471, h2338, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2340_1, u2elo3]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h0, h2333, hc01, hc14, hlam, hphi, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2288, hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2331, hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2288, h2338, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2340_1, u2elo3]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h0, h2338, hc01, hlam, hphi, ht12, p2340_1, u2elo3]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2338, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2340_1, u2elo3]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2336, hlam, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2338, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2340_1, u2elo3]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2336, hc23, hc35, hlam, hphi, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [hlam, p2340_0]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          rcases p2340_3 (m.d 0 5) (by simp) with h2360 | h2360
                          · linarith only [h2025, h2360, hlam]
                          · linarith only [h2238, h2360, hlam]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2238, hlam, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2333, hlam, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2338, hlam, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [h2339, hlam, p2340_1]
                        · have p2340_0 := h2340c.1
                          have p2340_1 := h2340c.2.1
                          have p2340_2 := h2340c.2.2.1
                          have p2340_3 := h2340c.2.2.2
                          linarith only [hlam, p2340_0]
                      · linarith only [h0, h2238, h2239, h2288, h2290, h2339, hc12, hlam, hphi, u2elo4]
                    · linarith only [h2239, h2290, h2333, h2334, h2338, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h2238, h2333, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2371 | h2371
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2372 | h2372
        · linarith only [h1471, h2372, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2374 | h2374
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2375 | h2375
            · linarith only [h2025, h2371, h2372, h2375, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2377 | h2377
              · linarith only [h2238, h2371, h2372, h2374, h2377, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2379 | h2379
                · linarith only [h2371, h2372, h2379, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h2371, h2372, h2374, h2379, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2382 | h2382
            · linarith only [h2025, h2371, h2372, h2382, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2384 | h2384
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2385 | h2385
                · linarith only [h2371, h2372, h2374, h2385, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2387 | h2387
                  · linarith only [h0, h2382, h2387, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2389 | h2389
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2390 | h2390
                      · rcases h5bigk with h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1471, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2025, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2238, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2372, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2382, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2238, h2372, h2389, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2391_1, u2elo3]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, h2389, hc01, hlam, hphi, ht12, p2391_1, u2elo3]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2389, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2391_1, u2elo3]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2387, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2238, h2389, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2391_1, u2elo3]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, h2371, h2372, h2389, hc01, hc23, hc35, hlam, hphi, ht12, p2391_1, u2elo3]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2371, h2372, hc23, hc35, hlam, hphi, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2238, h2371, h2372, h2389, h2390, hc04, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2391_1, u2elo3]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, h2384, hc01, hc14, hlam, hphi, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2384, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2389, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2390, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                      · linarith only [h2371, h2374, h2389, h2390, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h2371, h2372, h2374, h2384, h2389, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2419 | h2419
                · linarith only [h2371, h2372, h2419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2421 | h2421
                  · linarith only [h2371, h2372, h2421, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2423 | h2423
                    · linarith only [h0, h2384, h2423, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2425 | h2425
                      · linarith only [h2371, h2372, h2423, h2425, hc23, hc34, hlam, hphi]
                      · rcases h5bigk with h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, hlam, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h1471, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2025, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2238, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2372, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2382, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2384, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p2427_1, u2elo4]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2427_1, u2elo4]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2421, hlam, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2423, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, h2425, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h1471, h2425, hc02, hc45, hlam, hphi, ht23, ht34, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2425, hlam, p2427_0]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2371, h2372, hc23, hc45, hlam, hphi, ht34, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [h2025, hc03, hc45, hlam, hphi, ht34, p2427_1]
                        · have p2427_0 := h2427c.1
                          have p2427_1 := h2427c.2.1
                          have p2427_2 := h2427c.2.2.1
                          have p2427_3 := h2427c.2.2.2
                          linarith only [hlam, p2427_0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2453 | h2453
        · linarith only [h1471, h2371, h2453, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2455 | h2455
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2456 | h2456
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2457 | h2457
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2458 | h2458
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2459 | h2459
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2460 | h2460
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2461 | h2461
                      · linarith only [h2238, h2371, h2455, h2461, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases h5bigk with h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h0, hlam, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h1471, hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2025, hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2238, hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2453, hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2025, h2453, h2458, h2460, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2463_1, u2elo2]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2025, h2453, h2458, h2460, h2461, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2463_1, u2elo2]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h0, h2458, h2460, hc01, hlam, hphi, ht12, p2463_1, u2elo2]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2458, h2460, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2463_1, u2elo2]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2025, h2458, h2460, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2463_1, u2elo2]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2025, h2458, h2460, h2461, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2463_1, u2elo2]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2456, hlam, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2459, hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2461, hlam, p2463_0]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2457, hlam, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2460, hlam, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [h2025, hc03, hc45, hlam, hphi, ht34, p2463_1]
                        · have p2463_0 := h2463c.1
                          have p2463_1 := h2463c.2.1
                          have p2463_2 := h2463c.2.2.1
                          have p2463_3 := h2463c.2.2.2
                          linarith only [hlam, p2463_0]
                    · linarith only [h2371, h2453, h2455, h2457, h2460, hc12, hlam, hphi, u2elo2]
                  · linarith only [h2371, h2456, h2459, hlam]
                · linarith only [h2025, h2371, h2456, h2458, hc03, hc34, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2492 | h2492
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2493 | h2493
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2494 | h2494
                    · linarith only [h0, h2457, h2494, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2496 | h2496
                      · linarith only [h2455, h2457, h2496, hlam]
                      · rcases h5bigk with h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h0, hlam, p2498_1]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h1471, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2025, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2238, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2498_1]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2453, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2025, h2371, h2456, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2498_1, u2elo2]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2457, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p2498_1, u2elo4]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2498_1, u2elo4]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2025, h2493, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2498_1, u2elo2]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2494, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2498_1]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2456, hlam, p2498_1]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2493, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2496, hlam, p2498_0]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2498_1]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h0, h2025, h2371, h2456, hc01, hc03, hc45, hlam, hphi, ht12, ht34, p2498_1, u2elo2]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h1471, h2025, h2371, h2456, hc02, hc03, hc45, hlam, hphi, ht34, p2498_1, u2elo2]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [h2025, hc03, hc45, hlam, hphi, ht34, p2498_1]
                        · have p2498_0 := h2498c.1
                          have p2498_1 := h2498c.2.1
                          have p2498_2 := h2498c.2.2.1
                          have p2498_3 := h2498c.2.2.2
                          linarith only [hlam, p2498_0]
                  · linarith only [h2371, h2456, h2493, hlam]
                · linarith only [h2371, h2455, h2492, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2526 | h2526
              · linarith only [h2455, h2456, h2526, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2528 | h2528
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2529 | h2529
                  · linarith only [h2455, h2456, h2529, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2531 | h2531
                    · linarith only [h0, h2526, h2531, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2533 | h2533
                      · linarith only [h0, h2453, h2455, h2531, h2533, hc01, hc13, hlam, hphi]
                      · rcases h5bigk with h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c | h2535c
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, hlam, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h1471, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2025, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2238, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2453, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2456, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2526, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p2535_1, u2elo4]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2535_1, u2elo4]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2529, hlam, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2531, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, h2533, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h1471, h2533, hc02, hc45, hlam, hphi, ht23, ht34, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2533, hlam, p2535_0]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h0, h2453, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [h2025, hc03, hc45, hlam, hphi, ht34, p2535_1]
                        · have p2535_0 := h2535c.1
                          have p2535_1 := h2535c.2.1
                          have p2535_2 := h2535c.2.2.1
                          have p2535_3 := h2535c.2.2.2
                          linarith only [hlam, p2535_0]
                · linarith only [h2371, h2455, h2528, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2562 | h2562
            · linarith only [h2025, h2455, h2562, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2564 | h2564
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2565 | h2565
                · linarith only [h2371, h2455, h2565, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2567 | h2567
                  · linarith only [h0, h2562, h2565, h2567, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2569 | h2569
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2570 | h2570
                      · rcases h5bigk with h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c | h2571c
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h0, hlam, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h1471, hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2025, hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2238, hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2453, hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2562, hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2238, h2453, h2569, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2571_1, u2elo3]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h0, h2569, hc01, hlam, hphi, ht12, p2571_1, u2elo3]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2569, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2571_1, u2elo3]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2567, hlam, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2238, h2569, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2571_1, u2elo3]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2567, hc23, hc35, hlam, hphi, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [hlam, p2571_0]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2238, h2570, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h0, h2564, hc01, hc14, hlam, hphi, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2564, hlam, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2569, hlam, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [h2570, hlam, p2571_1]
                        · have p2571_0 := h2571c.1
                          have p2571_1 := h2571c.2.1
                          have p2571_2 := h2571c.2.2.1
                          have p2571_3 := h2571c.2.2.2
                          linarith only [hlam, p2571_0]
                      · linarith only [h2371, h2455, h2569, h2570, hc12, hlam, hphi, u2elo3]
                    · linarith only [h2371, h2455, h2564, h2565, h2569, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2599 | h2599
                · linarith only [h2371, h2455, h2599, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2601 | h2601
                  · linarith only [h2025, h2599, h2601, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2603 | h2603
                    · linarith only [h2371, h2455, h2564, h2603, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2605 | h2605
                      · linarith only [h2371, h2599, h2603, h2605, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h2371, h2599, h2605, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1471 | h1471
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x1_x0 m hb1 hb2 hb4 hb5 h0 h1471
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x1_x1 m hb1 hb2 hb4 hb5 h0 h1471

set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
