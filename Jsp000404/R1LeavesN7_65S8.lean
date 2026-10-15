import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S7

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_25_L_0_M_LI_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
  · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
    · rcases m.htr 1 2 5 (by decide) (by decide) with h456 | h456
      · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
        · linarith only [h0, h3, h457, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h459 | h459
          · linarith only [h0, h3, h455, h459, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h461 | h461
            · rcases m.htr 3 4 5 (by decide) (by decide) with h462 | h462
              · rcases h5bigk with h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc15, hlam, hphi, p463_1, u5elo0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h461, hc45, hlam, hphi, p463_1, u5elo0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h3, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc45, hlam, hphi, p463_1, u5elo0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h1, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h461, hc45, hlam, hphi, p463_1, u5elo1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h457, hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h1, h3, hc45, hlam, hphi, p463_1, u5elo3]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h2, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h456, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h459, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc45, hlam, hphi, p463_1, u5elo2]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc05, hlam, hphi, p463_1, u5elo3]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc15, hlam, hphi, p463_1, u5elo3]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc25, hlam, hphi, p463_1, u5elo3]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hc45, hlam, hphi, p463_1, u5elo3]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h454, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h455, h457, h461, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p463_1, u2elo3]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h461, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [h462, hlam, p463_1]
                · have p463_0 := h463c.1
                  have p463_1 := h463c.2.1
                  have p463_2 := h463c.2.2.1
                  have p463_3 := h463c.2.2.2
                  linarith only [hlam, p463_0]
              · linarith only [h1, h3, h456, h461, h462, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h490 | h490
              · rcases h5bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hc15, hlam, hphi, p491_1, u5elo0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h3, hc25, hlam, hphi, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h3, hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h3, h461, hc24, hlam, hphi, ht45, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h1, hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hc25, hlam, hphi, p491_1, u5elo1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h457, hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h1, h3, h461, hc24, hlam, hphi, ht45, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h2, hlam, p491_1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h456, hlam, p491_1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h459, hlam, p491_1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h461, hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hc05, hlam, hphi, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h456, h459, hc23, hlam, hphi, ht34, ht45, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h459, hc23, hlam, hphi, ht34, ht45, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hlam, p491_0]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h461, hc24, hlam, hphi, ht45, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h454, hlam, p491_1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h456, h459, h490, hc23, hc34, hlam, hphi, p491_1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h3, h454, h459, hc23, hlam, hphi, ht34, ht45, p491_1, u5elo3]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [h490, hlam, p491_1]
                · have p491_0 := h491c.1
                  have p491_1 := h491c.2.1
                  have p491_2 := h491c.2.2.1
                  have p491_3 := h491c.2.2.2
                  linarith only [hlam, p491_0]
              · linarith only [h3, h454, h490, hlam]
      · linarith only [h2, h456, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h519 | h519
      · linarith only [h0, h3, h455, h519, hc25, hlam, hphi, u5elo3]
      · linarith only [h2, h519, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
    · rcases m.htr 1 2 5 (by decide) (by decide) with h523 | h523
      · rcases m.htr 1 3 5 (by decide) (by decide) with h524 | h524
        · linarith only [h0, h3, h524, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h526 | h526
          · linarith only [h3, h522, h526, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h528 | h528
            · linarith only [h1, h454, h523, h528, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h530 | h530
              · rcases h5bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h523, hc25, hlam, hphi, p531_1, u5elo0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h454, h530, hc25, hlam, hphi, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h3, hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h454, hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h1, hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hc25, hlam, hphi, p531_1, u5elo1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h524, hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h1, h454, hlam, p531_1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h2, hlam, p531_1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h523, hlam, p531_1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h526, hlam, p531_1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h528, hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hc05, hlam, hphi, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h523, h526, hc23, hlam, hphi, ht34, ht45, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h526, hc23, hlam, hphi, ht34, ht45, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hlam, p531_0]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h454, hc04, hlam, hphi, ht45, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h3, h530, hc03, hc34, hlam, hphi, p531_1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h523, h526, h530, hc23, hlam, hphi, ht34, ht45, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h526, h530, hc23, hlam, hphi, ht34, ht45, p531_1, u5elo3]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [h530, hlam, p531_1]
                · have p531_0 := h531c.1
                  have p531_1 := h531c.2.1
                  have p531_2 := h531c.2.2.1
                  have p531_3 := h531c.2.2.2
                  linarith only [hlam, p531_0]
              · rcases h5bigk with h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h523, h526, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h526, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h3, hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h454, hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h1, hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h526, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo1]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h524, hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h1, h3, h530, hlam, p557_1]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h2, hlam, p557_1]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h523, hlam, p557_1]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h526, hlam, p557_1]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h528, hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, p557_1, u5elo3]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h523, h526, h530, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo4]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h526, h530, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo4]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h530, hlam, p557_0]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h0, h3, h522, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo4]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h523, h526, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo4]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [h526, hc23, hlam, hphi, ht34, ht45, p557_1, u5elo4]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [hc35, hlam, hphi, p557_1, u5elo4]
                · have p557_0 := h557c.1
                  have p557_1 := h557c.2.1
                  have p557_2 := h557c.2.2.1
                  have p557_3 := h557c.2.2.2
                  linarith only [hlam, p557_0]
      · linarith only [h2, h523, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h584 | h584
      · linarith only [h0, h3, h522, h584, hc25, hlam, hphi, u5elo3]
      · linarith only [h2, h584, hc12, hlam, hphi, u2elo0]

theorem r1l7_12_25_L_0_M_LI_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_12_25_L_0_M_LI_x0_x0_x0_x0 m hb2 hb5 h0 h1 h2 h3
  · exact r1l7_12_25_L_0_M_LI_x0_x0_x0_x1 m hb2 hb5 h0 h1 h2 h3

theorem r1l7_12_25_L_0_M_LI_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h587 | h587
  · rcases m.htr 0 4 5 (by decide) (by decide) with h588 | h588
    · rcases m.htr 1 2 3 (by decide) (by decide) with h589 | h589
      · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
        · linarith only [h2, h590, hc02, hlam, hphi, u2elo1]
        · linarith only [h589, h590, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
        · linarith only [h2, h589, h593, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
          · rcases m.htr 2 3 5 (by decide) (by decide) with h596 | h596
            · rcases m.htr 2 4 5 (by decide) (by decide) with h597 | h597
              · rcases m.htr 3 4 5 (by decide) (by decide) with h598 | h598
                · rcases h5bigk with h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hc15, hlam, hphi, p599_1, u5elo0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h2, hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h2, h598, hc45, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h2, hc45, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h1, hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h593, hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h598, hc45, hlam, hphi, p599_1, u5elo1]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h1, h2, hc45, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hc05, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hc15, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h598, hc45, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hc45, hlam, hphi, p599_1, u5elo2]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h587, hlam, p599_1]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h595, hlam, p599_1]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h596, hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hlam, p599_0]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hc45, hlam, hphi, p599_1, u5elo3]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h588, hlam, p599_1]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hc15, hlam, hphi, p599_1, u5elo4]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h597, hlam, p599_1]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [h598, hlam, p599_1]
                  · have p599_0 := h599c.1
                    have p599_1 := h599c.2.1
                    have p599_2 := h599c.2.2.1
                    have p599_3 := h599c.2.2.2
                    linarith only [hlam, p599_0]
                · rcases h5bigk with h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h2, h593, hc12, hlam, hphi, ht23, ht34, ht45, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h2, hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h2, h598, hc34, hlam, hphi, ht45, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h2, hc45, hlam, hphi, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h1, hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h593, hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h598, hc34, hlam, hphi, ht45, p625_1, u5elo1]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h1, h2, h598, hc34, hlam, hphi, ht45, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hc05, hlam, hphi, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hc15, hlam, hphi, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h598, hc34, hlam, hphi, ht45, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h598, hc34, hlam, hphi, ht45, p625_1, u5elo2]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h587, hlam, p625_1]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h595, hlam, p625_1]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h596, hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h598, hlam, p625_0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h588, hlam, p625_1]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h588, h593, hc12, hlam, hphi, ht23, ht34, ht45, p625_1, u5elo0]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h597, hlam, p625_1]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [h597, h598, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u2elo3]
                  · have p625_0 := h625c.1
                    have p625_1 := h625c.2.1
                    have p625_2 := h625c.2.2.1
                    have p625_3 := h625c.2.2.2
                    linarith only [hlam, p625_0]
              · linarith only [h2, h588, h597, hlam]
            · linarith only [h2, h587, h589, h596, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
            · linarith only [h589, h595, h653, hc12, hlam, hphi, u2elo2]
            · linarith only [h589, h653, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
      · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
        · linarith only [h2, h657, hc02, hlam, hphi, u2elo1]
        · linarith only [h656, h657, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
        · linarith only [h2, h656, h660, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
          · rcases m.htr 2 3 5 (by decide) (by decide) with h663 | h663
            · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
              · rcases m.htr 3 4 5 (by decide) (by decide) with h665 | h665
                · linarith only [h1, h588, h662, h665, hlam]
                · rcases h5bigk with h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h588, h664, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p667_1, u2elo3]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h2, hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h588, h664, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p667_1, u2elo3]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h588, hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h1, hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h660, hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hc35, hlam, hphi, p667_1, u5elo1]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h1, h588, hlam, p667_1]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hc05, hlam, hphi, p667_1, u5elo2]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hc15, hlam, hphi, p667_1, u5elo2]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h665, hc34, hlam, hphi, ht45, p667_1, u5elo2]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h588, hc04, hlam, hphi, ht45, p667_1, u5elo2]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h587, hlam, p667_1]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h662, hlam, p667_1]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h663, hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h665, hlam, p667_0]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h1, h660, hc12, hlam, hphi, ht23, ht34, ht45, p667_1, u5elo4]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h660, h664, hc12, hlam, hphi, p667_1, u2elo3]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h664, hlam, p667_1]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [h664, h665, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p667_1, u2elo3]
                  · have p667_0 := h667c.1
                    have p667_1 := h667c.2.1
                    have p667_2 := h667c.2.2.1
                    have p667_3 := h667c.2.2.2
                    linarith only [hlam, p667_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h693 | h693
                · linarith only [h2, h587, h664, h693, hlam]
                · rcases h5bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h662, hc35, hlam, hphi, p695_1, u5elo0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h2, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h2, h664, hc35, hlam, hphi, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h588, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h1, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h660, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hc35, hlam, hphi, p695_1, u5elo1]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h1, h2, h664, hlam, p695_1]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h664, hc05, hlam, hphi, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h664, hc15, hlam, hphi, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h664, h693, hc34, hlam, hphi, ht45, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h664, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h587, hlam, p695_1]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h662, hlam, p695_1]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h663, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h693, hlam, p695_0]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h1, h660, hc12, hlam, hphi, ht23, ht34, ht45, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h660, hc12, hlam, hphi, ht23, ht34, ht45, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hc25, hlam, hphi, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [h693, hc34, hlam, hphi, ht45, p695_1, u5elo4]
                  · have p695_0 := h695c.1
                    have p695_1 := h695c.2.1
                    have p695_2 := h695c.2.2.1
                    have p695_3 := h695c.2.2.2
                    linarith only [hlam, p695_0]
            · linarith only [h2, h587, h656, h663, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h722 | h722
            · linarith only [h656, h662, h722, hc12, hlam, hphi, u2elo2]
            · linarith only [h656, h722, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h725 | h725
    · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
      · rcases m.htr 1 2 5 (by decide) (by decide) with h727 | h727
        · linarith only [h2, h727, hc02, hlam, hphi, u2elo1]
        · linarith only [h726, h727, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h730 | h730
        · linarith only [h0, h587, h726, h730, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
          · linarith only [h0, h587, h732, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
            · linarith only [h0, h587, h726, h734, hc12, hlam, hphi, u2elo2]
            · linarith only [h726, h734, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
      · rcases m.htr 1 2 5 (by decide) (by decide) with h738 | h738
        · linarith only [h2, h738, hc02, hlam, hphi, u2elo1]
        · linarith only [h737, h738, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h741 | h741
        · linarith only [h0, h587, h737, h741, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
          · linarith only [h0, h587, h743, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h745 | h745
            · linarith only [h0, h587, h737, h745, hc12, hlam, hphi, u2elo2]
            · linarith only [h737, h745, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

theorem r1l7_12_25_L_0_M_LI_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_12_25_L_0_M_LI_x0_x0_x0 m hb2 hb5 h0 h1 h2
  · exact r1l7_12_25_L_0_M_LI_x0_x0_x1 m hb2 hb5 h0 h1 h2

theorem r1l7_12_25_L_0_M_LI_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  linarith only [h0, h1, hc13, hlam, hphi, ht34, ht45, u5elo1]

theorem r1l7_12_25_L_0_M_LI_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_12_25_L_0_M_LI_x0_x0 m hb2 hb5 h0 h1
  · exact r1l7_12_25_L_0_M_LI_x0_x1 m hb2 hb5 h0 h1

theorem r1l7_12_25_L_0_M_LI_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h749 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h750 | h750
  · rcases m.htr 0 3 5 (by decide) (by decide) with h751 | h751
    · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
      · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
        · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
          · rcases m.htr 1 3 5 (by decide) (by decide) with h755 | h755
            · rcases m.htr 2 3 5 (by decide) (by decide) with h756 | h756
              · rcases m.htr 2 4 5 (by decide) (by decide) with h757 | h757
                · rcases m.htr 3 4 5 (by decide) (by decide) with h758 | h758
                  · rcases h5bigk with h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [hlam, p759_0]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, h754, h756, h758, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, h756, h758, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, h758, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h749, hlam, p759_0]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [hlam, p759_0]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h756, h758, hc45, hlam, hphi, p759_1, u5elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, h758, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h750, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h754, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [hlam, p759_0]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h758, hc45, hlam, hphi, p759_1, u5elo2]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h0, h749, h753, h754, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h751, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h755, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h756, hlam, p759_0]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [hlam, p759_0]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h756, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo2]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h752, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h757, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u2elo3]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h757, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [h758, hlam, p759_1]
                    · have p759_0 := h759c.1
                      have p759_1 := h759c.2.1
                      have p759_2 := h759c.2.2.1
                      have p759_3 := h759c.2.2.2
                      linarith only [hlam, p759_0]
                  · linarith only [h0, h749, h753, h754, h757, h758, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h786 | h786
                  · linarith only [h0, h749, h753, h755, h757, h786, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases h5bigk with h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h753, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h753, h756, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h753, h757, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h749, hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h756, hc35, hlam, hphi, p788_1, u5elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h753, h757, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h750, hlam, p788_1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h754, hlam, p788_1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h786, hc34, hlam, hphi, ht45, p788_1, u5elo2]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h757, hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h751, hlam, p788_1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h755, hlam, p788_1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h756, hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h786, hlam, p788_0]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h752, hlam, p788_1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [hc15, hlam, hphi, p788_1, u5elo4]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h752, h753, h756, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [h0, h749, h752, h753, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p788_1, u2elo1]
                    · have p788_0 := h788c.1
                      have p788_1 := h788c.2.1
                      have p788_2 := h788c.2.2.1
                      have p788_3 := h788c.2.2.2
                      linarith only [hlam, p788_0]
              · linarith only [h0, h749, h753, h755, h756, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · linarith only [h0, h755, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h749, h753, h754, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h817 | h817
          · rcases m.htr 1 3 5 (by decide) (by decide) with h818 | h818
            · rcases m.htr 2 3 5 (by decide) (by decide) with h819 | h819
              · rcases m.htr 2 4 5 (by decide) (by decide) with h820 | h820
                · rcases m.htr 3 4 5 (by decide) (by decide) with h821 | h821
                  · rcases h5bigk with h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hlam, p822_0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h817, h819, h821, hc45, hlam, hphi, p822_1, u5elo0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h819, h821, hc45, hlam, hphi, p822_1, u5elo0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h821, hc45, hlam, hphi, p822_1, u5elo0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hc45, hlam, hphi, p822_1, u5elo0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h749, hlam, p822_0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hlam, p822_0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h819, h821, hc45, hlam, hphi, p822_1, u5elo1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h0, h749, h753, h821, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p822_1, u2elo2]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h0, h749, h753, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p822_1, u2elo2]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h750, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h817, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hlam, p822_0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h821, hc45, hlam, hphi, p822_1, u5elo2]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h0, h749, h753, h817, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p822_1, u2elo2]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h751, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h818, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h819, hlam, p822_0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hlam, p822_0]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hc45, hlam, hphi, p822_1, u5elo3]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h752, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h820, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p822_1, u2elo3]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h820, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [h821, hlam, p822_1]
                    · have p822_0 := h822c.1
                      have p822_1 := h822c.2.1
                      have p822_2 := h822c.2.2.1
                      have p822_3 := h822c.2.2.2
                      linarith only [hlam, p822_0]
                  · linarith only [h0, h749, h753, h817, h820, h821, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h849 | h849
                  · linarith only [h0, h749, h753, h818, h820, h849, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases h5bigk with h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c | h851c
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h753, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h753, h819, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h753, h820, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h749, hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h819, hc35, hlam, hphi, p851_1, u5elo1]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h753, h820, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h750, hlam, p851_1]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h817, hlam, p851_1]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h849, hc34, hlam, hphi, ht45, p851_1, u5elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h820, hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h751, hlam, p851_1]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h818, hlam, p851_1]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h819, hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h849, hlam, p851_0]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h752, hlam, p851_1]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [hc15, hlam, hphi, p851_1, u5elo4]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h752, h753, h819, h849, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [h0, h749, h752, h753, h849, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p851_1, u2elo2]
                    · have p851_0 := h851c.1
                      have p851_1 := h851c.2.1
                      have p851_2 := h851c.2.2.1
                      have p851_3 := h851c.2.2.2
                      linarith only [hlam, p851_0]
              · linarith only [h0, h753, h819, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h749, h751, h818, hlam]
          · linarith only [h750, h817, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h880 | h880
        · rcases m.htr 1 2 5 (by decide) (by decide) with h881 | h881
          · rcases m.htr 1 3 5 (by decide) (by decide) with h882 | h882
            · rcases m.htr 2 3 5 (by decide) (by decide) with h883 | h883
              · rcases m.htr 2 4 5 (by decide) (by decide) with h884 | h884
                · linarith only [h749, h752, h881, h884, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                  · linarith only [h0, h749, h752, h880, h881, h883, h886, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases h5bigk with h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hc15, hlam, hphi, p888_1, u5elo0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h0, h749, h880, h883, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p888_1, u2elo1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h0, h749, h880, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p888_1, u2elo1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h752, hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h749, hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h0, h749, h880, h883, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p888_1, u2elo1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h0, h749, h880, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p888_1, u2elo1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h0, h749, h752, h880, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p888_1, u2elo1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h750, hlam, p888_1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h881, hlam, p888_1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h886, hc34, hlam, hphi, ht45, p888_1, u5elo2]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h884, hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h751, hlam, p888_1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h882, hlam, p888_1]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h883, hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h886, hlam, p888_0]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hc05, hlam, hphi, p888_1, u5elo4]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h881, h883, h886, hc34, hlam, hphi, ht45, p888_1, u5elo4]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h883, h886, hc34, hlam, hphi, ht45, p888_1, u5elo4]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [h886, hc34, hlam, hphi, ht45, p888_1, u5elo4]
                    · have p888_0 := h888c.1
                      have p888_1 := h888c.2.1
                      have p888_2 := h888c.2.2.1
                      have p888_3 := h888c.2.2.2
                      linarith only [hlam, p888_0]
              · linarith only [h0, h749, h880, h882, h883, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · linarith only [h0, h882, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h880, h881, hc01, hlam, hphi, ht12, u2elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h917 | h917
          · rcases m.htr 1 3 5 (by decide) (by decide) with h918 | h918
            · rcases m.htr 2 3 5 (by decide) (by decide) with h919 | h919
              · rcases m.htr 2 4 5 (by decide) (by decide) with h920 | h920
                · linarith only [h749, h752, h917, h920, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h922 | h922
                  · linarith only [h751, h752, h922, hlam]
                  · rcases h5bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hc15, hlam, hphi, p924_1, u5elo0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h749, h880, h919, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h749, h880, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h752, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h749, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h749, h880, h919, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h749, h880, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h749, h880, h920, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h750, hlam, p924_1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h917, hlam, p924_1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h922, hc34, hlam, hphi, ht45, p924_1, u5elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h920, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h751, hlam, p924_1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h918, hlam, p924_1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h919, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h922, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hc05, hlam, hphi, p924_1, u5elo4]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hc15, hlam, hphi, p924_1, u5elo4]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h919, h922, hc34, hlam, hphi, ht45, p924_1, u5elo4]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h922, hc34, hlam, hphi, ht45, p924_1, u5elo4]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
              · linarith only [h0, h880, h919, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h749, h751, h918, hlam]
          · linarith only [h750, h917, hc12, hlam, hphi, u2elo0]
    · linarith only [h0, h749, h751, hc15, hlam, hphi, u5elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h954 | h954
    · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
      · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
        · rcases m.htr 1 2 5 (by decide) (by decide) with h957 | h957
          · linarith only [h750, h957, hc02, hlam, hphi, u2elo1]
          · linarith only [h956, h957, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h960 | h960
          · linarith only [h750, h960, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h749, h956, h960, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h963 | h963
        · rcases m.htr 1 2 5 (by decide) (by decide) with h964 | h964
          · linarith only [h750, h964, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h963, h964, hc01, hlam, hphi, ht12, u2elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h967 | h967
          · linarith only [h750, h963, h967, hc02, hlam, hphi, u2elo2]
          · linarith only [h0, h749, h963, h967, hc12, hlam, hphi, u2elo2]
    · linarith only [h0, h749, h954, hc15, hlam, hphi, u5elo3]

end R2N4
