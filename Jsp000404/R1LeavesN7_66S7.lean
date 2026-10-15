import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S5
import Jsp000404.R1LeavesN7_66S6

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_0_L_0_H_I_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h688 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1032 | h1032
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1033 | h1033
    · linarith only [h1033, h688, hc02, hlam, hphi, u2elo1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1035 | h1035
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1036 | h1036
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1037 | h1037
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1038 | h1038
            · rcases h5bigk with h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h0, hlam, p1039_1]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h688, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p1039_1, u0elo4]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1032, hc45, hlam, hphi, ht0b, ht5b, p1039_1, u0elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1033, h1036, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1033, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1033, h1036, h1038, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1033, h1036, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h0, h1036, hc01, hlam, hphi, ht12, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1036, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1036, h1038, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1036, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1039_1, u2elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1032, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1035, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1036, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1032, hc45, hlam, hphi, ht0b, ht5b, p1039_1, u0elo2]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1039_1]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h0, h1038, hc01, hc34, hlam, hphi, ht12, ht23, p1039_1]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1037, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [h1038, hlam, p1039_0]
              · have p1039_0 := h1039c.1
                have p1039_1 := h1039c.2.1
                have p1039_2 := h1039c.2.2.1
                have p1039_3 := h1039c.2.2.2
                linarith only [hlam, p1039_0]
            · rcases h5bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h0, hlam, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h688, hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p1065_1, u0elo4]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h0, h1033, h1036, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1033, h1036, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1033, hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1033, h1036, h1038, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1033, h1036, h1038, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h0, h1036, hc01, hlam, hphi, ht12, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1036, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1036, h1038, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1036, h1038, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1065_1, u2elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1032, hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1035, hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1036, hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1038, hlam, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h0, h1037, hc01, hlam, hphi, ht12, p1065_1, u2elo3]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1037, hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1037, h1038, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1065_1, u2elo3]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1091 | h1091
            · linarith only [h1032, h1037, h1091, h688, hlam]
            · rcases h5bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h0, hlam, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h688, hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h0, h1033, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1093_1, u2elo4]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h0, h1033, h1037, hlam, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1033, h1036, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1093_1, u2elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1033, hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1033, h1036, h1091, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1, u2elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1033, h1037, hlam, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h0, h1036, hc01, hlam, hphi, ht12, p1093_1, u2elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1036, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1093_1, u2elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1036, h1091, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1, u2elo2]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1037, hlam, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1032, hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1035, hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1036, hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1091, hlam, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h688, hc02, hc45, hlam, hphi, ht23, ht34, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [h1091, hc34, hc45, hlam, hphi, p1093_1]
              · have p1093_0 := h1093c.1
                have p1093_1 := h1093c.2.1
                have p1093_2 := h1093c.2.2.1
                have p1093_3 := h1093c.2.2.2
                linarith only [hlam, p1093_0]
        · linarith only [h0, h1032, h1033, h1036, hlam]
      · linarith only [h0, h1032, h1035, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1121 | h1121
    · linarith only [h1121, h688, hc02, hlam, hphi, u2elo1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1123 | h1123
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1124 | h1124
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1126 | h1126
            · rcases h5bigk with h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, hlam, p1127_1]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h688, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1032, hlam, p1127_1]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1032, h1124, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo2]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1121, h1125, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1121, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1032, h1121, h1125, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1121, h1125, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, h1125, hc01, hlam, hphi, ht12, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1125, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1032, h1125, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1125, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo3]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, h1123, hc01, hc13, hlam, hphi, p1127_1]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1123, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1124, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1124, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo2]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1127_1]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1124, h1126, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1, u2elo2]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1125, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [h1126, hlam, p1127_0]
              · have p1127_0 := h1127c.1
                have p1127_1 := h1127c.2.1
                have p1127_2 := h1127c.2.2.1
                have p1127_3 := h1127c.2.2.2
                linarith only [hlam, p1127_0]
            · rcases h5bigk with h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h0, hlam, p1153_1]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h688, hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, hlam, p1153_1]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, h1126, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1153_1, u0elo4]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p1153_1]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1121, hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, h1121, h1125, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, h1121, h1125, h1126, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h0, h1125, hc01, hlam, hphi, ht12, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1125, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, h1125, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, h1125, h1126, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1153_1]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1123, hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1124, hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1126, hlam, p1153_1]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h0, h1125, hc01, hlam, hphi, ht12, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1125, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1125, hlam, p1153_0]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [h1032, h1125, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1153_1, u2elo3]
              · have p1153_0 := h1153c.1
                have p1153_1 := h1153c.2.1
                have p1153_2 := h1153c.2.2.1
                have p1153_3 := h1153c.2.2.2
                linarith only [hlam, p1153_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1179 | h1179
            · linarith only [h1121, h1123, h1125, h1179, hlam]
            · rcases h5bigk with h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h0, hlam, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h688, hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1032, hlam, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1121, h1125, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1181_1, u0elo4]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1121, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1181_1, u2elo4]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1121, hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1121, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1181_1, u2elo4]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1121, h1125, hlam, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h0, h1124, hc01, hlam, hphi, ht12, p1181_1, u2elo2]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1124, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1181_1, u2elo2]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1032, h1124, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1181_1, u2elo2]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1125, hlam, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1123, hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1124, hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [hlam, p1181_0]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1179, hlam, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1121, hc12, hc45, hlam, hphi, ht23, ht34, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [h1179, hc34, hc45, hlam, hphi, p1181_1]
              · have p1181_0 := h1181c.1
                have p1181_1 := h1181c.2.1
                have p1181_2 := h1181c.2.2.1
                have p1181_3 := h1181c.2.2.2
                linarith only [hlam, p1181_0]
        · linarith only [h1121, h1123, h1124, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1208 | h1208
        · linarith only [h0, h1123, h1208, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1210 | h1210
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1211 | h1211
            · rcases h5bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h0, hlam, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h688, hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1032, hlam, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p1212_1, u0elo4]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1121, h1210, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1212_1, u2elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1121, hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1123, hlam, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1121, h1210, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1212_1, u2elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h0, h1210, hc01, hlam, hphi, ht12, p1212_1, u2elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1212_1, u2elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1208, hlam, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1212_1, u2elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h0, h1211, hc01, hc34, hlam, hphi, ht12, ht23, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h0, h1211, hc01, hc34, hlam, hphi, ht12, ht23, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1211, h688, hc02, hc34, hlam, hphi, ht23, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                rcases p1212_3 (m.d 0 5) (by simp) with h1232 | h1232
                · linarith only [h1032, h1232, hlam]
                · linarith only [h0, h1211, h1232, hc01, hc34, hlam, hphi, ht12, ht23, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1212_1]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h0, h1210, hc01, hlam, hphi, ht12, p1212_1, u2elo3]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1210, hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [h1211, hlam, p1212_0]
              · have p1212_0 := h1212c.1
                have p1212_1 := h1212c.2.1
                have p1212_2 := h1212c.2.2.1
                have p1212_3 := h1212c.2.2.2
                linarith only [hlam, p1212_0]
            · linarith only [h0, h1123, h1210, h1211, hc01, hlam, hphi, ht12, u2elo3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1241 | h1241
            · rcases h5bigk with h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, hlam, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h688, hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1032, hlam, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, h1121, h1210, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1242_1, u0elo4]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1121, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1242_1, u2elo4]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1121, hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1123, hlam, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1121, h1210, hlam, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, h1210, h1241, hc01, hc34, hlam, hphi, ht12, ht23, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1210, h1241, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1208, hlam, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1210, hlam, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h688, hc02, hc35, hlam, hphi, ht23, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1210, h1241, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, h1241, hc01, hc34, hlam, hphi, ht12, ht23, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h0, h1121, h1241, hc01, hc34, hlam, hphi, ht12, ht23, p1242_1]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [h1241, hlam, p1242_0]
              · have p1242_0 := h1242c.1
                have p1242_1 := h1242c.2.1
                have p1242_2 := h1242c.2.2.1
                have p1242_3 := h1242c.2.2.2
                linarith only [hlam, p1242_0]
            · rcases h5bigk with h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [hlam, p1268_0]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h688, hlam, p1268_0]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1032, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1241, hc34, hlam, hphi, ht0b, ht45, ht5b, p1268_1, u0elo4]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1121, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1268_1, u2elo4]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [hlam, p1268_0]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1121, hlam, p1268_0]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1123, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1121, h1208, h1241, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p1268_1, u2elo4]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p1268_1, u2elo4]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [hlam, p1268_0]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1208, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1210, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, h1241, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1241, h688, hc02, hc45, hlam, hphi, ht23, ht34, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [hlam, p1268_0]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1241, hlam, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h0, h1121, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [h1032, hc03, hc45, hlam, hphi, ht34, p1268_1]
              · have p1268_0 := h1268c.1
                have p1268_1 := h1268c.2.1
                have p1268_2 := h1268c.2.2.1
                have p1268_3 := h1268c.2.2.2
                linarith only [hlam, p1268_0]

theorem r1l7_10_12_25_L_0_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h688 | h688
  · exact r1l7_10_12_25_L_0_L_0_H_I_x1_x0 m hb0 hb2 hb5 h0 h688
  · exact r1l7_10_12_25_L_0_L_0_H_I_x1_x1 m hb0 hb2 hb5 h0 h688

theorem r1l7_10_12_25_L_0_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_25_L_0_L_0_H_I_x0 m hb0 hb2 hb5 h0
  · exact r1l7_10_12_25_L_0_L_0_H_I_x1 m hb0 hb2 hb5 h0

end R2N4
