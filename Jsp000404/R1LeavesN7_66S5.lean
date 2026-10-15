import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S4

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_0_L_0_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h345 | h345
  · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
    · linarith only [h1, h346, hc02, hlam, hphi, u2elo1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
      · rcases m.htr 2 3 5 (by decide) (by decide) with h349 | h349
        · rcases m.htr 2 4 5 (by decide) (by decide) with h350 | h350
          · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
            · rcases h5bigk with h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p352_1, u0elo4]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h1, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h345, hc35, hlam, hphi, ht0b, ht5b, p352_1, u0elo2]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h1, h349, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p352_1, u2elo2]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h0, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h346, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h0, h351, hc45, hlam, hphi, ht0b, ht5b, p352_1, u0elo0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p352_1, u0elo0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h349, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p352_1, u2elo2]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h349, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p352_1, u2elo2]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h349, h351, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p352_1, u2elo2]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h349, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p352_1, u2elo2]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h345, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h348, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h349, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h348, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p352_1]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p352_1]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h348, h351, hlam, p352_1]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h350, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [h351, hlam, p352_0]
              · have p352_0 := h352c.1
                have p352_1 := h352c.2.1
                have p352_2 := h352c.2.2.1
                have p352_3 := h352c.2.2.2
                linarith only [hlam, p352_0]
            · rcases h5bigk with h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c | h378c
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p378_1, u0elo4]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h1, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h1, h349, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p378_1, u2elo2]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h1, h349, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p378_1, u2elo2]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h0, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h346, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h0, h351, hc34, hlam, hphi, ht0b, ht45, ht5b, p378_1, u0elo0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h0, h351, hc34, hlam, hphi, ht0b, ht45, ht5b, p378_1, u0elo0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h349, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p378_1, u2elo2]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h349, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p378_1, u2elo2]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h349, h351, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p378_1, u2elo2]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h349, h351, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p378_1, u2elo2]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h345, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h348, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h349, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h351, hlam, p378_1]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h0, h346, hc12, hc45, hlam, hphi, ht23, ht34, p378_1]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h350, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p378_1, u2elo3]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h350, hlam, p378_0]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [h350, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p378_1, u2elo3]
              · have p378_0 := h378c.1
                have p378_1 := h378c.2.1
                have p378_2 := h378c.2.2.1
                have p378_3 := h378c.2.2.2
                linarith only [hlam, p378_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
            · linarith only [h1, h345, h350, h404, hlam]
            · rcases h5bigk with h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c | h406c
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p406_1, u0elo4]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h1, hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo4]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h1, h350, hlam, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h0, hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h346, hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h0, h404, hc34, hlam, hphi, ht0b, ht45, ht5b, p406_1, u0elo0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h0, h1, h350, hc05, hlam, hphi, ht0b, ht5b, p406_1, u0elo0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo4]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo4]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h349, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p406_1, u2elo2]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h350, hlam, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h345, hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h348, hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h349, hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hlam, p406_0]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h404, hlam, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h0, h346, hc12, hc45, hlam, hphi, ht23, ht34, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h346, hc12, hc45, hlam, hphi, ht23, ht34, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [h404, hc34, hc45, hlam, hphi, p406_1]
              · have p406_0 := h406c.1
                have p406_1 := h406c.2.1
                have p406_2 := h406c.2.2.1
                have p406_3 := h406c.2.2.2
                linarith only [hlam, p406_0]
        · linarith only [h0, h1, h348, h349, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h433 | h433
        · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
          · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
            · rcases h5bigk with h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p436_1, u0elo4]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h1, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h1, h348, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u2elo4]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h1, h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h0, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h346, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h348, hlam, p436_1]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p436_1, u0elo0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h433, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h433, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h348, h433, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h345, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h345, h346, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p436_1, u0elo4]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h433, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h433, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h0, h346, hc12, hc45, hlam, hphi, ht23, ht34, p436_1]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h346, h433, h435, hc12, hlam, hphi, p436_1, u2elo2]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h434, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [h435, hlam, p436_0]
              · have p436_0 := h436c.1
                have p436_1 := h436c.2.1
                have p436_2 := h436c.2.2.1
                have p436_3 := h436c.2.2.2
                linarith only [hlam, p436_0]
            · rcases h5bigk with h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h346, h348, h434, h435, hc12, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p462_1, u0elo4, u2elo3]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h1, hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h1, h348, h433, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p462_1, u2elo2]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h1, h348, h433, h435, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p462_1, u2elo2]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h0, hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h346, hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h348, hlam, p462_1]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h348, h435, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p462_1]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h433, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p462_1, u2elo2]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h433, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p462_1, u2elo2]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h348, h433, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p462_1, u2elo2]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h348, h433, h435, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p462_1, u2elo2]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h345, hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h345, h346, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p462_1, u0elo4]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h433, hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h435, hlam, p462_1]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h434, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p462_1, u2elo3]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h346, h434, hc12, hlam, hphi, p462_1, u2elo3]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h434, hlam, p462_0]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [h434, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p462_1, u2elo3]
              · have p462_0 := h462c.1
                have p462_1 := h462c.2.1
                have p462_2 := h462c.2.2.1
                have p462_3 := h462c.2.2.2
                linarith only [hlam, p462_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
            · linarith only [h1, h345, h434, h488, hlam]
            · rcases h5bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h346, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p490_1, u0elo4]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h1, hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p490_1, u2elo4]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h1, h434, hlam, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h0, hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h346, hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h348, hlam, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h434, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p490_1, u2elo4]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p490_1, u2elo4]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h348, h433, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p490_1, u2elo2]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h434, hlam, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h345, hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h345, h346, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p490_1, u0elo4]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h433, hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hlam, p490_0]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h488, hlam, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h0, h346, hc12, hc45, hlam, hphi, ht23, ht34, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h346, hc12, hc45, hlam, hphi, ht23, ht34, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [h488, hc34, hc45, hlam, hphi, p490_1]
              · have p490_0 := h490c.1
                have p490_1 := h490c.2.1
                have p490_2 := h490c.2.2.1
                have p490_3 := h490c.2.2.2
                linarith only [hlam, p490_0]
        · linarith only [h1, h345, h433, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
    · linarith only [h1, h517, hc02, hlam, hphi, u2elo1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
      · linarith only [h0, h345, h519, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
        · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
          · rcases m.htr 3 4 5 (by decide) (by decide) with h523 | h523
            · rcases h5bigk with h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [hc15, hlam, hphi, ht0b, ht5b, p524_1, u0elo4]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h1, hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h345, hlam, p524_1]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h345, h521, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p524_1, u2elo2]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h0, hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h517, hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h519, hlam, p524_1]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p524_1, u0elo0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h522, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p524_1, u2elo3]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h522, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p524_1, u2elo3]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h345, h522, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u2elo3]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h522, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p524_1, u2elo3]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h0, h517, h523, hc12, hc34, hlam, hphi, ht23, p524_1]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h517, h523, hc12, hc34, hlam, hphi, ht23, p524_1]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h521, hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h521, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p524_1, u2elo2]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h0, h517, hc12, hc45, hlam, hphi, ht23, ht34, p524_1]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h517, h521, h523, hc12, hlam, hphi, p524_1, u2elo2]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h522, hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [h523, hlam, p524_0]
              · have p524_0 := h524c.1
                have p524_1 := h524c.2.1
                have p524_2 := h524c.2.2.1
                have p524_3 := h524c.2.2.2
                linarith only [hlam, p524_0]
            · rcases h5bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h517, h519, h522, h523, hc12, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u0elo4, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h1, hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h345, hlam, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h345, h523, hlam, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h0, hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h517, hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h519, hlam, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h519, h523, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h522, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h522, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h519, h522, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h519, h522, h523, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h0, h517, hc12, hc35, hlam, hphi, ht23, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h517, h523, hc12, hc45, hlam, hphi, ht23, ht34, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h521, hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h523, hlam, p550_1]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h0, h517, h522, hc12, hlam, hphi, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h517, h522, hc12, hlam, hphi, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h522, hlam, p550_0]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [h345, h522, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p550_1, u2elo3]
              · have p550_0 := h550c.1
                have p550_1 := h550c.2.1
                have p550_2 := h550c.2.2.1
                have p550_3 := h550c.2.2.2
                linarith only [hlam, p550_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h576 | h576
            · linarith only [h1, h521, h522, h576, hc02, hlam, hphi, u2elo2]
            · rcases h5bigk with h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h517, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p578_1, u0elo4]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h1, hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h345, hlam, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h1, h345, h521, h522, hc02, hlam, hphi, p578_1, u2elo2]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h0, hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h517, hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h519, hlam, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h1, h522, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p578_1, u2elo4]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p578_1, u2elo4]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h521, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p578_1, u2elo2]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h522, hlam, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h0, h517, hc12, hc35, hlam, hphi, ht23, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h517, hc12, hc35, hlam, hphi, ht23, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h521, hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [hlam, p578_0]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h576, hlam, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h0, h517, hc12, hc45, hlam, hphi, ht23, ht34, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h517, hc12, hc45, hlam, hphi, ht23, ht34, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [h576, hc34, hc45, hlam, hphi, p578_1]
              · have p578_0 := h578c.1
                have p578_1 := h578c.2.1
                have p578_2 := h578c.2.2.1
                have p578_3 := h578c.2.2.2
                linarith only [hlam, p578_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h604 | h604
          · rcases m.htr 3 4 5 (by decide) (by decide) with h605 | h605
            · rcases h5bigk with h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h517, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p606_1, u0elo4]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h1, hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h345, hlam, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p606_1, u0elo4]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h0, hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h517, hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h519, hlam, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p606_1, u0elo0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h604, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p606_1, u2elo3]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h604, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p606_1, u2elo3]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h521, hlam, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h604, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p606_1, u2elo3]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h0, h517, h605, hc12, hc34, hlam, hphi, ht23, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h517, h605, hc12, hc34, hlam, hphi, ht23, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h1, h605, hc02, hc34, hlam, hphi, ht23, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                rcases p606_3 (m.d 0 5) (by simp) with h626 | h626
                · linarith only [h345, h626, hlam]
                · linarith only [h0, h517, h605, h626, hc12, hc34, hlam, hphi, ht23, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h0, h517, hc12, hc45, hlam, hphi, ht23, ht34, p606_1]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h517, h604, hc12, hlam, hphi, p606_1, u2elo3]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h604, hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [h605, hlam, p606_0]
              · have p606_0 := h606c.1
                have p606_1 := h606c.2.1
                have p606_2 := h606c.2.2.1
                have p606_3 := h606c.2.2.2
                linarith only [hlam, p606_0]
            · linarith only [h1, h521, h604, h605, hc02, hlam, hphi, u2elo3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h635 | h635
            · rcases h5bigk with h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h517, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p636_1, u0elo4]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h1, hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h345, hlam, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h1, h604, hlam, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h0, hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h517, hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h519, hlam, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h1, h604, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p636_1, u2elo4]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h604, h635, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h521, hlam, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h604, hlam, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h1, hc02, hc35, hlam, hphi, ht23, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h517, hc12, hc35, hlam, hphi, ht23, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h1, hc02, hc35, hlam, hphi, ht23, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h604, h635, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h0, h517, hc12, hc45, hlam, hphi, ht23, ht34, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h517, h635, hc12, hc34, hlam, hphi, ht23, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h1, h635, hc02, hc34, hlam, hphi, ht23, p636_1]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [h635, hlam, p636_0]
              · have p636_0 := h636c.1
                have p636_1 := h636c.2.1
                have p636_2 := h636c.2.2.1
                have p636_3 := h636c.2.2.2
                linarith only [hlam, p636_0]
            · rcases h5bigk with h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h517, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p662_1, u0elo4]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h1, hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h345, hlam, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h635, hc34, hlam, hphi, ht0b, ht45, ht5b, p662_1, u0elo4]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h0, hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h517, hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h519, hlam, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h1, h521, h635, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p662_1, u2elo4]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p662_1, u2elo4]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h521, hlam, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h604, hlam, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h1, hc02, hc35, hlam, hphi, ht23, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h517, h635, hc12, hc45, hlam, hphi, ht23, ht34, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h1, h635, hc02, hc45, hlam, hphi, ht23, ht34, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hlam, p662_0]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h635, hlam, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h0, h517, hc12, hc45, hlam, hphi, ht23, ht34, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h517, hc12, hc45, hlam, hphi, ht23, ht34, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [h345, hc03, hc45, hlam, hphi, ht34, p662_1]
              · have p662_0 := h662c.1
                have p662_1 := h662c.2.1
                have p662_2 := h662c.2.2.1
                have p662_3 := h662c.2.2.2
                linarith only [hlam, p662_0]

theorem r1l7_10_12_25_L_0_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_25_L_0_L_0_H_I_x0_x0 m hb0 hb2 hb5 h0 h1
  · exact r1l7_10_12_25_L_0_L_0_H_I_x0_x1 m hb0 hb2 hb5 h0 h1

end R2N4
