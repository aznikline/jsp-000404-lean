import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S8

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_25_L_0_M_LI_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h749 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h971 | h971
  · rcases m.htr 0 3 5 (by decide) (by decide) with h972 | h972
    · rcases m.htr 0 4 5 (by decide) (by decide) with h973 | h973
      · rcases m.htr 1 2 3 (by decide) (by decide) with h974 | h974
        · rcases m.htr 1 2 5 (by decide) (by decide) with h975 | h975
          · rcases m.htr 1 3 5 (by decide) (by decide) with h976 | h976
            · rcases m.htr 2 3 5 (by decide) (by decide) with h977 | h977
              · rcases m.htr 2 4 5 (by decide) (by decide) with h978 | h978
                · rcases m.htr 3 4 5 (by decide) (by decide) with h979 | h979
                  · rcases h5bigk with h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hlam, p980_0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h749, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h977, h979, hc45, hlam, hphi, p980_1, u5elo0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h979, hc45, hlam, hphi, p980_1, u5elo0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h749, hc45, hlam, hphi, p980_1, u5elo1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hc05, hlam, hphi, p980_1, u5elo1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hlam, p980_0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h977, h979, hc45, hlam, hphi, p980_1, u5elo1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h979, hc45, hlam, hphi, p980_1, u5elo1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hc45, hlam, hphi, p980_1, u5elo1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h971, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h975, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hlam, p980_0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h971, h979, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p980_1, u2elo0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h971, hc45, hlam, hphi, p980_1, u5elo0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h972, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h976, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h977, hlam, p980_0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hlam, p980_0]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h974, h977, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h973, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h749, hc05, hlam, hphi, p980_1, u5elo4]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h978, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [h979, hlam, p980_1]
                    · have p980_0 := h980c.1
                      have p980_1 := h980c.2.1
                      have p980_2 := h980c.2.2.1
                      have p980_3 := h980c.2.2.2
                      linarith only [hlam, p980_0]
                  · rcases h5bigk with h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hlam, p1006_0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h749, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h978, h979, hc34, hlam, hphi, ht45, p1006_1, u5elo0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h749, hc35, hlam, hphi, p1006_1, u5elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h749, h979, hc34, hlam, hphi, ht45, p1006_1, u5elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hc05, hlam, hphi, p1006_1, u5elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hlam, p1006_0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h978, h979, hc34, hlam, hphi, ht45, p1006_1, u5elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hc35, hlam, hphi, p1006_1, u5elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h979, hc34, hlam, hphi, ht45, p1006_1, u5elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h971, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h975, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hlam, p1006_0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h971, h979, hc34, hlam, hphi, ht45, p1006_1, u5elo0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h974, h977, h979, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1006_1, u2elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h972, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h976, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h977, hlam, p1006_0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hlam, p1006_0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h979, hlam, p1006_0]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h973, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h749, h978, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1006_1, u2elo3]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h978, hlam, p1006_1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [h974, h977, h978, h979, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1006_1, u2elo1]
                    · have p1006_0 := h1006c.1
                      have p1006_1 := h1006c.2.1
                      have p1006_2 := h1006c.2.2.1
                      have p1006_3 := h1006c.2.2.2
                      linarith only [hlam, p1006_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1032 | h1032
                  · linarith only [h1032, h974, h977, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases h5bigk with h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h749, hlam, p1034_1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hc25, hlam, hphi, p1034_1, u5elo0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h749, hc35, hlam, hphi, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h749, h978, hc24, hlam, hphi, ht45, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hc05, hlam, hphi, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hc25, hlam, hphi, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hc35, hlam, hphi, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h978, hc24, hlam, hphi, ht45, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h971, hlam, p1034_1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h975, hlam, p1034_1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h1032, hc34, hlam, hphi, ht45, p1034_1, u5elo2]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h978, hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h972, hlam, p1034_1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h976, hlam, p1034_1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h977, hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h1032, hlam, p1034_0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h973, hlam, p1034_1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h973, hc15, hlam, hphi, p1034_1, u5elo0]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hc25, hlam, hphi, p1034_1, u5elo4]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [h1032, h749, h973, hc34, hlam, hphi, ht45, p1034_1, u5elo1]
                    · have p1034_0 := h1034c.1
                      have p1034_1 := h1034c.2.1
                      have p1034_2 := h1034c.2.2.1
                      have p1034_3 := h1034c.2.2.2
                      linarith only [hlam, p1034_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1060 | h1060
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1061 | h1061
                  · rcases h5bigk with h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hlam, p1062_0]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h749, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h749, hc25, hlam, hphi, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h749, h977, hc23, hlam, hphi, ht34, ht45, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h749, hc45, hlam, hphi, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hc05, hlam, hphi, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hlam, p1062_0]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h1060, hc45, hlam, hphi, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h977, hc23, hlam, hphi, ht34, ht45, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hc45, hlam, hphi, p1062_1, u5elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h971, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h975, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hlam, p1062_0]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h977, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hc45, hlam, hphi, p1062_1, u5elo2]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h972, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h976, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hc25, hlam, hphi, p1062_1, u5elo3]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hlam, p1062_0]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h0, h972, h974, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1062_1, u2elo1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h973, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hc15, hlam, hphi, p1062_1, u5elo4]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h1060, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [h1061, hlam, p1062_1]
                    · have p1062_0 := h1062c.1
                      have p1062_1 := h1062c.2.1
                      have p1062_2 := h1062c.2.2.1
                      have p1062_3 := h1062c.2.2.2
                      linarith only [hlam, p1062_0]
                  · linarith only [h1060, h1061, h977, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1089 | h1089
                  · rcases h5bigk with h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hlam, p1090_0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h749, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hc25, hlam, hphi, p1090_1, u5elo0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h749, h977, hc23, hlam, hphi, ht34, ht45, p1090_1, u5elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h1060, h749, hc24, hlam, hphi, ht45, p1090_1, u5elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hc05, hlam, hphi, p1090_1, u5elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hlam, p1090_0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hc25, hlam, hphi, p1090_1, u5elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h977, hc23, hlam, hphi, ht34, ht45, p1090_1, u5elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h1060, hc24, hlam, hphi, ht45, p1090_1, u5elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h971, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h975, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hlam, p1090_0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h977, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h1060, hlam, p1090_0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h972, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h976, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h972, h977, hc23, hlam, hphi, ht34, ht45, p1090_1, u5elo0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hlam, p1090_0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h0, h1060, h972, h974, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1090_1, u2elo1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h973, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h749, hc05, hlam, hphi, p1090_1, u5elo4]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h973, h977, hc23, hlam, hphi, ht34, ht45, p1090_1, u5elo0]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [h1089, hlam, p1090_1]
                    · have p1090_0 := h1090c.1
                      have p1090_1 := h1090c.2.1
                      have p1090_2 := h1090c.2.2.1
                      have p1090_3 := h1090c.2.2.2
                      linarith only [hlam, p1090_0]
                  · rcases h5bigk with h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h749, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h749, h977, hc23, hlam, hphi, ht34, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h749, h977, hc23, hlam, hphi, ht34, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1089, h749, hc34, hlam, hphi, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hc05, hlam, hphi, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h977, hc23, hlam, hphi, ht34, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h977, hc23, hlam, hphi, ht34, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1089, h977, hc23, hlam, hphi, ht34, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h971, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h975, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h977, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1060, hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h972, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h976, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h0, h972, h974, h977, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1116_1, u2elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h1089, hlam, p1116_0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h973, hlam, p1116_1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h973, hc15, hlam, hphi, p1116_1, u5elo0]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h749, h973, h977, hc23, hlam, hphi, ht34, ht45, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [h749, h973, hc35, hlam, hphi, p1116_1, u5elo1]
                    · have p1116_0 := h1116c.1
                      have p1116_1 := h1116c.2.1
                      have p1116_2 := h1116c.2.2.1
                      have p1116_3 := h1116c.2.2.2
                      linarith only [hlam, p1116_0]
            · linarith only [h0, h976, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h971, h975, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
          · linarith only [h1144, h749, h974, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h1144, h971, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1147 | h1147
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1148 | h1148
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1149 | h1149
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1150 | h1150
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1151 | h1151
                · linarith only [h1151, h971, h973, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1153 | h1153
                  · linarith only [h1153, h972, h973, hlam]
                  · rcases h5bigk with h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h749, hlam, p1155_1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc25, hlam, hphi, p1155_1, u5elo0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h973, hc35, hlam, hphi, p1155_1, u5elo4]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h973, hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc05, hlam, hphi, p1155_1, u5elo1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc25, hlam, hphi, p1155_1, u5elo1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc35, hlam, hphi, p1155_1, u5elo1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc45, hlam, hphi, p1155_1, u5elo1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h971, hlam, p1155_1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1148, hlam, p1155_1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1153, hc34, hlam, hphi, ht45, p1155_1, u5elo2]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1151, hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h972, hlam, p1155_1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1149, hlam, p1155_1]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1150, hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1153, hlam, p1155_0]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1155_1, u5elo4]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc15, hlam, hphi, p1155_1, u5elo4]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hc25, hlam, hphi, p1155_1, u5elo4]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [h1153, hc34, hlam, hphi, ht45, p1155_1, u5elo4]
                    · have p1155_0 := h1155c.1
                      have p1155_1 := h1155c.2.1
                      have p1155_2 := h1155c.2.2.1
                      have p1155_3 := h1155c.2.2.2
                      linarith only [hlam, p1155_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1181 | h1181
                · linarith only [h1181, h971, h973, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1183 | h1183
                  · linarith only [h1183, h972, h973, hlam]
                  · rcases h5bigk with h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h749, hlam, p1185_1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hc25, hlam, hphi, p1185_1, u5elo0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1150, h973, hc23, hlam, hphi, ht34, ht45, p1185_1, u5elo4]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h973, hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hc05, hlam, hphi, p1185_1, u5elo1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hc25, hlam, hphi, p1185_1, u5elo1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1150, hc23, hlam, hphi, ht34, ht45, p1185_1, u5elo1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1183, hc34, hlam, hphi, ht45, p1185_1, u5elo1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h971, hlam, p1185_1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1148, hlam, p1185_1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1150, hlam, p1185_1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1181, hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h972, hlam, p1185_1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1149, hlam, p1185_1]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1150, h972, hc23, hlam, hphi, ht34, ht45, p1185_1, u5elo0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1183, hlam, p1185_0]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hc05, hlam, hphi, p1185_1, u5elo4]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hc15, hlam, hphi, p1185_1, u5elo4]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1150, hc23, hlam, hphi, ht34, ht45, p1185_1, u5elo4]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [h1150, hc23, hlam, hphi, ht34, ht45, p1185_1, u5elo4]
                    · have p1185_0 := h1185c.1
                      have p1185_1 := h1185c.2.1
                      have p1185_2 := h1185c.2.2.1
                      have p1185_3 := h1185c.2.2.2
                      linarith only [hlam, p1185_0]
            · linarith only [h0, h1149, h972, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
          · linarith only [h1148, h971, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1213 | h1213
          · linarith only [h1147, h1213, h749, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h1213, h971, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1216 | h1216
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1217 | h1217
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1218 | h1218
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1219 | h1219
            · linarith only [h0, h1217, h1219, h972, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h0, h1219, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h1218, h971, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1223 | h1223
          · linarith only [h1217, h1223, h749, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h1223, h971, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1226 | h1226
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1227 | h1227
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1228 | h1228
            · linarith only [h0, h1226, h1228, h972, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h0, h1228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h1227, h971, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1232 | h1232
          · linarith only [h1226, h1232, h749, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h1232, h971, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1235 | h1235
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1236 | h1236
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1237 | h1237
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1238 | h1238
          · linarith only [h1238, h971, hc02, hlam, hphi, u2elo1]
          · linarith only [h1237, h1238, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1241 | h1241
          · linarith only [h1237, h1241, h971, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1243 | h1243
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1244 | h1244
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1245 | h1245
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1246 | h1246
                  · rcases h5bigk with h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h749, hlam, p1247_1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h971, hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1246, hc45, hlam, hphi, p1247_1, u5elo0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h749, hc45, hlam, hphi, p1247_1, u5elo1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hc05, hlam, hphi, p1247_1, u5elo1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1241, hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1241, h1246, hc45, hlam, hphi, p1247_1, u5elo2]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1241, hc45, hlam, hphi, p1247_1, u5elo2]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1247_1, u5elo2]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hc15, hlam, hphi, p1247_1, u5elo2]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1246, hc45, hlam, hphi, p1247_1, u5elo2]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hc45, hlam, hphi, p1247_1, u5elo2]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1235, hlam, p1247_1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1243, hlam, p1247_1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1244, hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hlam, p1247_0]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hc45, hlam, hphi, p1247_1, u5elo3]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1236, hlam, p1247_1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h749, hc05, hlam, hphi, p1247_1, u5elo4]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1245, hlam, p1247_1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [h1246, hlam, p1247_1]
                    · have p1247_0 := h1247c.1
                      have p1247_1 := h1247c.2.1
                      have p1247_2 := h1247c.2.2.1
                      have p1247_3 := h1247c.2.2.2
                      linarith only [hlam, p1247_0]
                  · rcases h5bigk with h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h749, hlam, p1273_1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h971, hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hc35, hlam, hphi, p1273_1, u5elo0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1246, h749, hc34, hlam, hphi, ht45, p1273_1, u5elo1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hc05, hlam, hphi, p1273_1, u5elo1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1241, hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1241, hc35, hlam, hphi, p1273_1, u5elo2]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1241, h1246, hc34, hlam, hphi, ht45, p1273_1, u5elo2]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1236, h1246, hc34, hlam, hphi, ht45, p1273_1, u5elo2]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hc15, hlam, hphi, p1273_1, u5elo2]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1246, hc34, hlam, hphi, ht45, p1273_1, u5elo2]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1246, hc34, hlam, hphi, ht45, p1273_1, u5elo2]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1235, hlam, p1273_1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1243, hlam, p1273_1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1244, hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1246, hlam, p1273_0]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1236, hlam, p1273_1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1236, h749, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1273_1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1245, hlam, p1273_1]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [h1245, h1246, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1273_1, u2elo3]
                    · have p1273_0 := h1273c.1
                      have p1273_1 := h1273c.2.1
                      have p1273_2 := h1273c.2.2.1
                      have p1273_3 := h1273c.2.2.2
                      linarith only [hlam, p1273_0]
                · linarith only [h1236, h1241, h1245, h749, hlam]
              · linarith only [h0, h1237, h1244, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h1235, h1243, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1302 | h1302
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1303 | h1303
          · linarith only [h1303, h971, hc02, hlam, hphi, u2elo1]
          · linarith only [h1302, h1303, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1306 | h1306
          · linarith only [h1302, h1306, h971, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1309 | h1309
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1310 | h1310
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1311 | h1311
                  · linarith only [h1235, h1236, h1311, hlam]
                  · rcases h5bigk with h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h749, hlam, p1313_1]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h971, hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1236, h1310, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1313_1, u2elo3]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1236, hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hc05, hlam, hphi, p1313_1, u5elo1]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1306, hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1306, hc35, hlam, hphi, p1313_1, u5elo2]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1236, h1306, hc04, hlam, hphi, ht45, p1313_1, u5elo2]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1313_1, u5elo2]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hc15, hlam, hphi, p1313_1, u5elo2]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1311, hc34, hlam, hphi, ht45, p1313_1, u5elo2]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1236, hc04, hlam, hphi, ht45, p1313_1, u5elo2]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1235, hlam, p1313_1]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1308, hlam, p1313_1]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1309, hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1311, hlam, p1313_0]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1313_1, u5elo4]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1310, h749, hc01, hlam, hphi, ht12, p1313_1, u2elo3]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1310, hlam, p1313_1]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [h1310, h1311, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1313_1, u2elo3]
                    · have p1313_0 := h1313c.1
                      have p1313_1 := h1313c.2.1
                      have p1313_2 := h1313c.2.2.1
                      have p1313_3 := h1313c.2.2.2
                      linarith only [hlam, p1313_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1339 | h1339
                  · linarith only [h0, h1235, h1302, h1306, h1310, h1339, h749, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases h5bigk with h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h749, hlam, p1341_1]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h971, hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1339, hc34, hlam, hphi, ht45, p1341_1, u5elo0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1236, hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hc05, hlam, hphi, p1341_1, u5elo1]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1306, hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1306, h1310, h1339, hc34, hlam, hphi, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1306, h1310, hlam, p1341_1]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1310, h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1310, h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1310, h1339, hc34, hlam, hphi, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1310, hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1235, hlam, p1341_1]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1308, hlam, p1341_1]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1309, hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1339, hlam, p1341_0]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h749, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hc25, hlam, hphi, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [h1339, hc34, hlam, hphi, ht45, p1341_1, u5elo4]
                    · have p1341_0 := h1341c.1
                      have p1341_1 := h1341c.2.1
                      have p1341_2 := h1341c.2.2.1
                      have p1341_3 := h1341c.2.2.2
                      linarith only [hlam, p1341_0]
              · linarith only [h0, h1302, h1309, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h1235, h1308, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1369 | h1369
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1370 | h1370
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1371 | h1371
          · linarith only [h1371, h971, hc02, hlam, hphi, u2elo1]
          · linarith only [h1370, h1371, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1374 | h1374
          · linarith only [h1370, h1374, h971, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1376 | h1376
            · linarith only [h0, h1235, h1370, h1376, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h0, h1376, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1379 | h1379
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1380 | h1380
          · linarith only [h1380, h971, hc02, hlam, hphi, u2elo1]
          · linarith only [h1379, h1380, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1383 | h1383
          · linarith only [h1379, h1383, h971, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
            · linarith only [h0, h1235, h1379, h1385, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h0, h1385, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem r1l7_12_25_L_0_M_LI_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h749 | h749
  · exact r1l7_12_25_L_0_M_LI_x1_x0 m hb2 hb5 h0 h749
  · exact r1l7_12_25_L_0_M_LI_x1_x1 m hb2 hb5 h0 h749

theorem r1l7_12_25_L_0_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_25_L_0_M_LI_x0 m hb2 hb5 h0
  · exact r1l7_12_25_L_0_M_LI_x1 m hb2 hb5 h0

end R2N4
