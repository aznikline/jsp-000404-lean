import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
  · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
    · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
      · linarith only [h1, h317, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
        · rcases m.htr 2 3 5 (by decide) (by decide) with h320 | h320
          · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
            · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
              · rcases h5bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hc15, hlam, hphi, p323_1, u5elo0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h1, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h322, hc45, hlam, hphi, p323_1, u5elo0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h1, hc45, hlam, hphi, p323_1, u5elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h0, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h317, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h322, hc45, hlam, hphi, p323_1, u5elo1]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h0, h1, hc45, hlam, hphi, p323_1, u5elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hc05, hlam, hphi, p323_1, u5elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hc15, hlam, hphi, p323_1, u5elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h322, hc45, hlam, hphi, p323_1, u5elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hc45, hlam, hphi, p323_1, u5elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h315, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h315, h317, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p323_1, u0elo2]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h320, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h315, hc45, hlam, hphi, p323_1, u5elo0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h316, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h319, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h321, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [h322, hlam, p323_0]
                · have p323_0 := h323c.1
                  have p323_1 := h323c.2.1
                  have p323_2 := h323c.2.2.1
                  have p323_3 := h323c.2.2.2
                  linarith only [hlam, p323_0]
              · rcases h5bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h1, h319, h322, hc34, hlam, hphi, ht45, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h1, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h1, h322, hc34, hlam, hphi, ht45, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h0, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h317, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h322, hc34, hlam, hphi, ht45, p349_1, u5elo1]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h322, hc34, hlam, hphi, ht45, p349_1, u5elo1]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hc05, hlam, hphi, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hc15, hlam, hphi, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h322, hc34, hlam, hphi, ht45, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h322, hc34, hlam, hphi, ht45, p349_1, u5elo2]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h315, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h319, h322, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p349_1, u3elo4]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h320, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h322, hlam, p349_1]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h316, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h319, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h321, hlam, p349_0]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [h321, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p349_1, u2elo3]
                · have p349_0 := h349c.1
                  have p349_1 := h349c.2.1
                  have p349_2 := h349c.2.2.1
                  have p349_3 := h349c.2.2.2
                  linarith only [hlam, p349_0]
            · linarith only [h0, h1, h319, h321, hlam]
          · linarith only [h315, h320, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
          · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
            · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
              · rcases h5bigk with h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h1, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h1, h319, h379, hc14, hlam, hphi, ht45, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h1, h319, hc14, hlam, hphi, ht45, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h0, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h317, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h319, h379, hc14, hlam, hphi, ht45, p380_1, u5elo1]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h319, hlam, p380_1]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hc05, hlam, hphi, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hc15, hlam, hphi, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h319, h379, hc14, hlam, hphi, ht45, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h319, hc14, hlam, hphi, ht45, p380_1, u5elo2]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h315, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h315, h317, hc12, hlam, hphi, ht23, p380_1, u3elo0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h377, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h315, h319, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p380_1, u3elo0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h316, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h317, h378, hc12, hlam, hphi, p380_1, u2elo3]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h378, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [h379, hlam, p380_0]
                · have p380_0 := h380c.1
                  have p380_1 := h380c.2.1
                  have p380_2 := h380c.2.2.1
                  have p380_3 := h380c.2.2.2
                  linarith only [hlam, p380_0]
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
                  linarith only [h317, hc12, hlam, hphi, ht23, ht34, ht45, p406_1, u5elo0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h1, hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, p406_1, u5elo2]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h1, h379, hc34, hlam, hphi, ht45, p406_1, u5elo2]
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
                  linarith only [h317, hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h379, hc34, hlam, hphi, ht45, p406_1, u5elo1]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h319, hlam, p406_1]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [hc05, hlam, hphi, p406_1, u5elo2]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [hc15, hlam, hphi, p406_1, u5elo2]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h379, hc34, hlam, hphi, ht45, p406_1, u5elo2]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h379, hc34, hlam, hphi, ht45, p406_1, u5elo2]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h315, hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h317, hc12, hlam, hphi, ht23, p406_1, u3elo4]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h377, hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h379, hlam, p406_1]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h316, hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h316, h317, hc12, hlam, hphi, ht23, ht34, ht45, p406_1, u5elo0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h378, hlam, p406_0]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [h378, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p406_1, u2elo3]
                · have p406_0 := h406c.1
                  have p406_1 := h406c.2.1
                  have p406_2 := h406c.2.2.1
                  have p406_3 := h406c.2.2.2
                  linarith only [hlam, p406_0]
            · linarith only [h1, h316, h378, hlam]
          · linarith only [h315, h377, hc23, hlam, hphi, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
      · linarith only [h1, h434, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
        · linarith only [h0, h316, h436, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
          · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
            · rcases m.htr 3 4 5 (by decide) (by decide) with h440 | h440
              · linarith only [h315, h316, h440, hlam]
              · rcases h5bigk with h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c | h442c
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h316, h439, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p442_1, u2elo3]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h1, hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h316, h439, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p442_1, u2elo3]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h316, hlam, p442_1]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h0, hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h434, hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h440, hc34, hlam, hphi, ht45, p442_1, u5elo1]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h436, hlam, p442_1]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hc05, hlam, hphi, p442_1, u5elo2]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hc15, hlam, hphi, p442_1, u5elo2]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h440, hc34, hlam, hphi, ht45, p442_1, u5elo2]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h316, hc04, hlam, hphi, ht45, p442_1, u5elo2]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h315, hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h434, hc12, hlam, hphi, ht23, p442_1, u3elo4]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h438, hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h440, hlam, p442_1]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h0, h434, hc12, hlam, hphi, ht23, ht34, ht45, p442_1, u5elo4]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h434, hc12, hlam, hphi, ht23, ht34, ht45, p442_1, u5elo4]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h439, hlam, p442_0]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [h439, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p442_1, u2elo3]
                · have p442_0 := h442c.1
                  have p442_1 := h442c.2.1
                  have p442_2 := h442c.2.2.1
                  have p442_3 := h442c.2.2.2
                  linarith only [hlam, p442_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
              · linarith only [h1, h439, h468, hc02, hlam, hphi, ht23, u3elo3]
              · rcases h5bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hc15, hlam, hphi, p470_1, u5elo0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h1, hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h468, hc34, hlam, hphi, ht45, p470_1, u5elo0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h316, hlam, p470_1]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h0, hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h434, hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h468, hc34, hlam, hphi, ht45, p470_1, u5elo1]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h436, hlam, p470_1]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h439, hc05, hlam, hphi, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h439, hc15, hlam, hphi, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h439, h468, hc34, hlam, hphi, ht45, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h439, hlam, p470_1]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h315, hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h434, hc12, hlam, hphi, ht23, p470_1, u3elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h438, hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hlam, p470_0]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h468, hlam, p470_1]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h0, h434, hc12, hlam, hphi, ht23, ht34, ht45, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [h434, hc12, hlam, hphi, ht23, ht34, ht45, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hc25, hlam, hphi, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hc35, hlam, hphi, p470_1, u5elo4]
                · have p470_0 := h470c.1
                  have p470_1 := h470c.2.1
                  have p470_2 := h470c.2.2.1
                  have p470_3 := h470c.2.2.2
                  linarith only [hlam, p470_0]
          · linarith only [h315, h438, hc23, hlam, hphi, u3elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h497 | h497
    · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
      · linarith only [h1, h498, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
        · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
          · linarith only [h315, h501, hc03, hlam, hphi, u3elo2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h503 | h503
            · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
              · rcases h5bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc15, hlam, hphi, p505_1, u5elo0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h315, hlam, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc45, hlam, hphi, p505_1, u5elo0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h498, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h1, h501, hc05, hlam, hphi, p505_1, u5elo1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, p505_1, u5elo0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc05, hlam, hphi, p505_1, u5elo2]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc15, hlam, hphi, p505_1, u5elo2]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h501, hlam, p505_1]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc45, hlam, hphi, p505_1, u5elo2]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h0, h498, hc12, hlam, hphi, ht23, ht34, ht45, p505_1, u5elo3]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h498, hc12, hlam, hphi, ht23, ht34, ht45, p505_1, u5elo3]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc25, hlam, hphi, p505_1, u5elo3]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hc45, hlam, hphi, p505_1, u5elo3]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h497, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h500, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h503, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [h504, hlam, p505_0]
                · have p505_0 := h505c.1
                  have p505_1 := h505c.2.1
                  have p505_2 := h505c.2.2.1
                  have p505_3 := h505c.2.2.2
                  linarith only [hlam, p505_0]
              · linarith only [h0, h315, h500, h504, hlam]
            · linarith only [h0, h1, h500, h503, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
          · linarith only [h315, h533, hc03, hlam, hphi, u3elo2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
            · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
              · rcases h5bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hc15, hlam, hphi, p537_1, u5elo0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h315, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, h500, h533, hc14, hlam, hphi, ht45, p537_1, u5elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h0, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h498, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h1, h533, hc05, hlam, hphi, p537_1, u5elo1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h500, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h315, h533, hc03, hlam, hphi, p537_1, u3elo4]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hc15, hlam, hphi, p537_1, u5elo2]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h533, hlam, p537_1]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h500, h533, hc14, hlam, hphi, ht45, p537_1, u5elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h497, h500, hc14, hlam, hphi, ht45, p537_1, u5elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h498, hc12, hlam, hphi, ht23, ht34, ht45, p537_1, u5elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hc25, hlam, hphi, p537_1, u5elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h500, hc14, hlam, hphi, ht45, p537_1, u5elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h497, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h498, h535, hc12, hlam, hphi, p537_1, u2elo3]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h535, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [h536, hlam, p537_0]
                · have p537_0 := h537c.1
                  have p537_1 := h537c.2.1
                  have p537_2 := h537c.2.2.1
                  have p537_3 := h537c.2.2.2
                  linarith only [hlam, p537_0]
              · linarith only [h315, h497, h536, hlam]
            · linarith only [h1, h497, h535, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h565 | h565
      · linarith only [h1, h565, hc02, hlam, hphi, u2elo1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
        · linarith only [h0, h497, h567, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
          · linarith only [h315, h569, hc03, hlam, hphi, u3elo2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
            · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
              · rcases h5bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h497, h572, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p573_1, u3elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h1, hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h315, hlam, p573_1]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h497, hlam, p573_1]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h0, hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h565, hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h1, h569, hc02, hlam, hphi, ht23, ht34, ht45, p573_1, u5elo1]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h567, hlam, p573_1]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, p573_1, u5elo2]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h569, hc15, hlam, hphi, p573_1, u5elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h569, hlam, p573_1]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h567, h569, hc14, hlam, hphi, ht45, p573_1, u5elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h0, h565, hc12, hlam, hphi, ht23, ht34, ht45, p573_1, u5elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h565, hc12, hlam, hphi, ht23, ht34, ht45, p573_1, u5elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [hc25, hlam, hphi, p573_1, u5elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h567, hc14, hlam, hphi, ht45, p573_1, u5elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h0, h565, h571, hc12, hlam, hphi, p573_1, u2elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h565, h571, hc12, hlam, hphi, p573_1, u2elo3]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h571, hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [h572, hlam, p573_0]
                · have p573_0 := h573c.1
                  have p573_1 := h573c.2.1
                  have p573_2 := h573c.2.2.1
                  have p573_3 := h573c.2.2.2
                  linarith only [hlam, p573_0]
              · linarith only [h1, h569, h571, h572, hc02, hlam, hphi, u2elo3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h600 | h600
              · linarith only [h1, h571, h600, hc02, hlam, hphi, ht23, u3elo3]
              · rcases h5bigk with h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h565, hc12, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h1, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h315, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h497, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h565, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h1, h569, hc02, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h567, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hc05, hlam, hphi, p602_1, u5elo2]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h569, h600, hc15, hlam, hphi, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h569, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h571, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h1, h600, hc02, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h565, h600, hc12, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h600, hc25, hlam, hphi, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h600, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, h565, hc12, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h565, hc12, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hc35, hlam, hphi, p602_1, u5elo4]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]

theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
