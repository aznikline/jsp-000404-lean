import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
  · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
    · rcases m.htr 1 3 4 (by decide) (by decide) with h324 | h324
      · rcases m.htr 1 3 5 (by decide) (by decide) with h325 | h325
        · rcases m.htr 1 4 5 (by decide) (by decide) with h326 | h326
          · rcases m.htr 2 3 4 (by decide) (by decide) with h327 | h327
            · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
              · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                · rcases h1bigk with h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h322, h327, h329, hc01, hc45, hlam, hphi, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h322, h327, h329, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h322, h327, h329, hc01, hc45, hlam, hphi, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    rcases p330_3 (m.d 0 1) (by simp) with h335 | h335
                    · rcases p330_3 (m.d 1 2) (by simp) with h336 | h336
                      · linarith only [h0, h336, hlam]
                      · linarith only [h323, h336, hlam]
                    · linarith only [h335, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h0, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h4, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h322, h327, h329, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h1, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h1, h322, h327, h329, hc01, hc45, hlam, hphi, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h1, h323, h328, hc01, hc35, hlam, hphi, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h2, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h322, hlam, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h324, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h2, h323, h328, hc01, hc35, hlam, hphi, ht0b, ht5b, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h3, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h323, hlam, p330_1]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h325, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [h326, hlam, p330_0]
                  · have p330_0 := h330c.1
                    have p330_1 := h330c.2.1
                    have p330_2 := h330c.2.2.1
                    have p330_3 := h330c.2.2.2
                    linarith only [hlam, p330_0]
                · rcases h1bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h322, h326, h329, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h322, h326, h329, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h326, h329, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h326, h329, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h0, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h4, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h326, h329, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h326, h329, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h1, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h322, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h1, h326, h329, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h1, h326, h329, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h2, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h322, hlam, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h324, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h322, h326, h329, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h3, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h323, hlam, p360_1]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h325, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [h326, hlam, p360_0]
                  · have p360_0 := h360c.1
                    have p360_1 := h360c.2.1
                    have p360_2 := h360c.2.2.1
                    have p360_3 := h360c.2.2.2
                    linarith only [hlam, p360_0]
              · linarith only [h328, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h324, h327, h4, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
            · rcases m.htr 2 3 5 (by decide) (by decide) with h389 | h389
              · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                · linarith only [h322, h326, h388, h390, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases h1bigk with h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c | h392c
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h322, h388, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h322, h388, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    rcases p392_3 (m.d 0 1) (by simp) with h396 | h396
                    · rcases p392_3 (m.d 1 2) (by simp) with h397 | h397
                      · linarith only [h0, h397, hlam]
                      · linarith only [h322, h397, hlam]
                    · linarith only [h396, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    rcases p392_3 (m.d 0 1) (by simp) with h401 | h401
                    · rcases p392_3 (m.d 1 2) (by simp) with h402 | h402
                      · linarith only [h0, h402, hlam]
                      · linarith only [h323, h402, hlam]
                    · linarith only [h401, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h0, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h4, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h0, h322, h388, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h1, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h1, h322, h388, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h1, h323, h389, h390, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h2, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h322, hlam, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h324, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h326, hlam, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h3, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h323, hlam, p392_1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h325, hlam, p392_0]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [h322, h388, hc34, hlam, hphi, ht45, p392_1, u5elo1]
                  · have p392_0 := h392c.1
                    have p392_1 := h392c.2.1
                    have p392_2 := h392c.2.2.1
                    have p392_3 := h392c.2.2.2
                    linarith only [hlam, p392_0]
              · linarith only [h389, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h323, h324, h388, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h322, h325, h4, hc24, hlam, hphi, ht45, u5elo3]
      · linarith only [h322, h324, h4, hlam]
    · linarith only [h322, h323, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
    · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
      · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
        · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
          · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
            · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
              · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                · rcases h1bigk with h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h431, h436, h437, hc01, hc45, hlam, hphi, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h432, h437, hc01, hc45, hlam, hphi, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h322, h431, h436, h437, hc01, hc45, hlam, hphi, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    rcases p438_3 (m.d 0 1) (by simp) with h443 | h443
                    · rcases p438_3 (m.d 1 2) (by simp) with h444 | h444
                      · linarith only [h0, h444, hlam]
                      · linarith only [h431, h444, hlam]
                    · linarith only [h443, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h0, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h4, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h322, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h322, h431, h435, h436, h437, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h1, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h1, h322, h431, h436, h437, hc01, hc45, hlam, hphi, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h1, h431, h436, h437, hc01, hc45, hlam, hphi, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h2, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h431, h436, h437, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h432, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h1, h431, h432, h436, h437, hc01, hc45, hlam, hphi, ht0b, ht5b, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h3, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h431, hlam, p438_1]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h433, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [h434, hlam, p438_0]
                  · have p438_0 := h438c.1
                    have p438_1 := h438c.2.1
                    have p438_2 := h438c.2.2.1
                    have p438_3 := h438c.2.2.2
                    linarith only [hlam, p438_0]
                · rcases h1bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h431, h436, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h322, h431, h432, h436, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h322, h431, h436, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h434, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h0, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h4, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h322, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h1, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h1, h434, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h1, h431, h436, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h2, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h431, h436, h437, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h432, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h1, h431, h432, h436, h437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h3, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h431, hlam, p468_1]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h433, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [h434, hlam, p468_0]
                  · have p468_0 := h468c.1
                    have p468_1 := h468c.2.1
                    have p468_2 := h468c.2.2.1
                    have p468_3 := h468c.2.2.2
                    linarith only [hlam, p468_0]
              · linarith only [h4, h436, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h4, h432, h435, hlam]
          · linarith only [h322, h431, h434, hc25, hlam, hphi, u5elo4]
        · linarith only [h432, h433, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h498 | h498
        · rcases m.htr 1 4 5 (by decide) (by decide) with h499 | h499
          · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
            · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
              · rcases m.htr 3 4 5 (by decide) (by decide) with h502 | h502
                · rcases h1bigk with h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h431, h501, h502, hc01, hc45, hlam, hphi, ht0b, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h4, h431, h501, h502, hc01, hc45, hlam, hphi, ht0b, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h4, h431, h432, h501, h502, hc01, hc45, hlam, hphi, ht0b, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    rcases p503_3 (m.d 0 1) (by simp) with h508 | h508
                    · rcases p503_3 (m.d 1 2) (by simp) with h509 | h509
                      · linarith only [h0, h509, hlam]
                      · linarith only [h431, h509, hlam]
                    · linarith only [h508, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h0, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h4, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h322, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h4, h432, h500, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h1, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h432, h500, hc12, hc23, hlam, hphi, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h432, hlam, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h431, h432, h500, h501, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h2, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h431, h432, h500, h501, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h432, h500, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h431, h432, h500, h501, h502, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h3, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h431, hlam, p503_1]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h498, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [h499, hlam, p503_0]
                  · have p503_0 := h503c.1
                    have p503_1 := h503c.2.1
                    have p503_2 := h503c.2.2.1
                    have p503_3 := h503c.2.2.2
                    linarith only [hlam, p503_0]
                · linarith only [h322, h431, h432, h502, hc25, hlam, hphi, u5elo4]
              · linarith only [h4, h431, h501, hc25, hlam, hphi, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
              · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                · rcases h1bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h431, h535, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h4, h431, h535, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h4, h431, h432, h535, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    rcases p537_3 (m.d 0 1) (by simp) with h542 | h542
                    · rcases p537_3 (m.d 1 2) (by simp) with h543 | h543
                      · linarith only [h0, h543, hlam]
                      · linarith only [h431, h543, hlam]
                    · linarith only [h542, hlam, p537_0]
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
                    linarith only [h4, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h322, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h4, h431, h500, h535, h536, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h1, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h432, hlam, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h4, h431, h500, h535, h536, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h2, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h2, h431, h535, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h2, h431, h535, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h3, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h431, hlam, p537_1]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h498, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [h499, hlam, p537_0]
                  · have p537_0 := h537c.1
                    have p537_1 := h537c.2.1
                    have p537_2 := h537c.2.2.1
                    have p537_3 := h537c.2.2.2
                    linarith only [hlam, p537_0]
                · linarith only [h4, h431, h500, h535, h536, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
              · linarith only [h4, h535, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h322, h431, h499, hc25, hlam, hphi, u5elo4]
        · linarith only [h4, h431, h498, hc25, hlam, hphi, u5elo3]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
      · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
        · rcases m.htr 1 4 5 (by decide) (by decide) with h573 | h573
          · rcases m.htr 2 3 4 (by decide) (by decide) with h574 | h574
            · rcases m.htr 2 3 5 (by decide) (by decide) with h575 | h575
              · rcases m.htr 3 4 5 (by decide) (by decide) with h576 | h576
                · rcases h1bigk with h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    rcases p577_3 (m.d 0 1) (by simp) with h579 | h579
                    · rcases p577_3 (m.d 1 2) (by simp) with h580 | h580
                      · linarith only [h580, hlam, p577_0]
                      · rcases p577_3 (m.d 1 3) (by simp) with h582 | h582
                        · linarith only [h1, h582, hlam]
                        · linarith only [h4, h582, hlam]
                    · linarith only [h579, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h571, h576, hc01, hc45, hlam, hphi, ht0b, ht5b, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h571, h576, hc01, hc45, hlam, hphi, ht0b, ht5b, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    rcases p577_3 (m.d 0 1) (by simp) with h588 | h588
                    · rcases p577_3 (m.d 1 2) (by simp) with h589 | h589
                      · linarith only [h0, h589, hlam]
                      · rcases p577_3 (m.d 1 3) (by simp) with h591 | h591
                        · linarith only [h1, h591, hlam]
                        · linarith only [h572, h591, hlam]
                    · linarith only [h588, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h0, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h4, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h322, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h431, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h1, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h2, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h571, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h1, h431, h571, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p577_1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h3, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p577_1, u5elo1]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h572, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [h573, hlam, p577_0]
                  · have p577_0 := h577c.1
                    have p577_1 := h577c.2.1
                    have p577_2 := h577c.2.2.1
                    have p577_3 := h577c.2.2.2
                    linarith only [hlam, p577_0]
                · rcases h1bigk with h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    rcases p615_3 (m.d 0 1) (by simp) with h617 | h617
                    · rcases p615_3 (m.d 1 2) (by simp) with h618 | h618
                      · linarith only [h618, hlam, p615_0]
                      · rcases p615_3 (m.d 1 3) (by simp) with h620 | h620
                        · linarith only [h1, h620, hlam]
                        · linarith only [h4, h620, hlam]
                    · linarith only [h617, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h573, h576, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h573, h576, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h0, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h4, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h322, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h431, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h1, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h1, h573, h576, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h2, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h322, hc12, hc24, hlam, hphi, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h571, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h1, h431, h571, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p615_1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h3, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p615_1, u5elo1]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h572, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [h573, hlam, p615_0]
                  · have p615_0 := h615c.1
                    have p615_1 := h615c.2.1
                    have p615_2 := h615c.2.2.1
                    have p615_3 := h615c.2.2.2
                    linarith only [hlam, p615_0]
              · linarith only [h4, h575, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h4, h571, h574, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h649 | h649
            · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
              · rcases m.htr 3 4 5 (by decide) (by decide) with h651 | h651
                · linarith only [h571, h573, h651, hlam]
                · rcases h1bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 1) (by simp) with h655 | h655
                    · rcases p653_3 (m.d 1 2) (by simp) with h656 | h656
                      · linarith only [h656, hlam, p653_0]
                      · rcases p653_3 (m.d 1 3) (by simp) with h658 | h658
                        · linarith only [h1, h658, hlam]
                        · linarith only [h4, h658, hlam]
                    · linarith only [h655, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h572, hc01, hc35, hlam, hphi, ht0b, ht5b, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 1) (by simp) with h663 | h663
                    · rcases p653_3 (m.d 1 2) (by simp) with h664 | h664
                      · linarith only [h0, h664, hlam]
                      · rcases p653_3 (m.d 1 3) (by simp) with h666 | h666
                        · linarith only [h1, h666, hlam]
                        · linarith only [h571, h666, hlam]
                    · linarith only [h663, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 1) (by simp) with h670 | h670
                    · rcases p653_3 (m.d 1 2) (by simp) with h671 | h671
                      · linarith only [h0, h671, hlam]
                      · rcases p653_3 (m.d 1 3) (by simp) with h673 | h673
                        · linarith only [h1, h673, hlam]
                        · linarith only [h572, h673, hlam]
                    · linarith only [h670, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h0, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h4, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h322, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h431, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h1, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h2, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h571, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h573, hlam, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h3, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p653_1, u5elo1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h572, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h3, hc14, hlam, hphi, ht45, p653_1, u5elo0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
              · linarith only [h4, h650, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h1, h4, h571, h649, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h571, h572, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h700 | h700
        · rcases m.htr 1 4 5 (by decide) (by decide) with h701 | h701
          · rcases m.htr 2 3 4 (by decide) (by decide) with h702 | h702
            · rcases m.htr 2 3 5 (by decide) (by decide) with h703 | h703
              · rcases m.htr 3 4 5 (by decide) (by decide) with h704 | h704
                · rcases h1bigk with h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    rcases p705_3 (m.d 0 1) (by simp) with h707 | h707
                    · rcases p705_3 (m.d 1 2) (by simp) with h708 | h708
                      · linarith only [h708, hlam, p705_0]
                      · rcases p705_3 (m.d 1 3) (by simp) with h710 | h710
                        · linarith only [h1, h710, hlam]
                        · linarith only [h4, h710, hlam]
                    · linarith only [h707, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h700, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h571, h700, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    rcases p705_3 (m.d 0 1) (by simp) with h716 | h716
                    · rcases p705_3 (m.d 1 2) (by simp) with h717 | h717
                      · linarith only [h0, h717, hlam]
                      · rcases p705_3 (m.d 1 3) (by simp) with h719 | h719
                        · linarith only [h1, h719, hlam]
                        · linarith only [h700, h719, hlam]
                    · linarith only [h716, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h0, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h4, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h322, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h431, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h1, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h571, h702, hc12, hc23, hlam, hphi, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h571, hlam, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h571, h702, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h2, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h571, h702, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h431, h571, h702, hc12, hc23, hlam, hphi, p705_1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h3, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p705_1, u5elo1]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h700, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [h701, hlam, p705_0]
                  · have p705_0 := h705c.1
                    have p705_1 := h705c.2.1
                    have p705_2 := h705c.2.2.1
                    have p705_3 := h705c.2.2.2
                    linarith only [hlam, p705_0]
                · linarith only [h571, h704, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h571, h700, h703, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h745 | h745
              · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                · rcases h1bigk with h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c | h747c
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    rcases p747_3 (m.d 0 1) (by simp) with h749 | h749
                    · rcases p747_3 (m.d 1 2) (by simp) with h750 | h750
                      · linarith only [h750, hlam, p747_0]
                      · rcases p747_3 (m.d 1 3) (by simp) with h752 | h752
                        · linarith only [h1, h752, hlam]
                        · linarith only [h4, h752, hlam]
                    · linarith only [h749, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h700, hc01, hc35, hlam, hphi, ht0b, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h571, h700, h746, hc01, hc45, hlam, hphi, ht0b, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    rcases p747_3 (m.d 0 1) (by simp) with h758 | h758
                    · rcases p747_3 (m.d 1 2) (by simp) with h759 | h759
                      · linarith only [h0, h759, hlam]
                      · rcases p747_3 (m.d 1 3) (by simp) with h761 | h761
                        · linarith only [h1, h761, hlam]
                        · linarith only [h700, h761, hlam]
                    · linarith only [h758, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h0, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h4, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h322, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h431, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h1, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h571, hlam, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h2, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h2, h431, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p747_1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h3, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p747_1, u5elo1]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h700, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [h701, hlam, p747_0]
                  · have p747_0 := h747c.1
                    have p747_1 := h747c.2.1
                    have p747_2 := h747c.2.2.1
                    have p747_3 := h747c.2.2.2
                    linarith only [hlam, p747_0]
                · linarith only [h571, h746, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h4, h745, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h571, h700, h701, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
          · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
            · rcases m.htr 2 3 5 (by decide) (by decide) with h790 | h790
              · rcases m.htr 3 4 5 (by decide) (by decide) with h791 | h791
                · rcases h1bigk with h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    rcases p792_3 (m.d 0 1) (by simp) with h794 | h794
                    · rcases p792_3 (m.d 1 2) (by simp) with h795 | h795
                      · linarith only [h795, hlam, p792_0]
                      · rcases p792_3 (m.d 1 3) (by simp) with h797 | h797
                        · linarith only [h1, h797, hlam]
                        · linarith only [h4, h797, hlam]
                    · linarith only [h794, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    rcases p792_3 (m.d 0 1) (by simp) with h801 | h801
                    · rcases p792_3 (m.d 1 2) (by simp) with h802 | h802
                      · linarith only [h0, h802, hlam]
                      · rcases p792_3 (m.d 1 3) (by simp) with h804 | h804
                        · linarith only [h804, hlam, p792_0]
                        · rcases p792_3 (m.d 1 4) (by simp) with h806 | h806
                          · linarith only [h2, h806, hlam]
                          · linarith only [h571, h806, hlam]
                    · linarith only [h801, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h788, hc01, hc45, hlam, hphi, ht0b, ht5b, p792_1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    rcases p792_3 (m.d 0 1) (by simp) with h811 | h811
                    · rcases p792_3 (m.d 1 2) (by simp) with h812 | h812
                      · linarith only [h0, h812, hlam]
                      · rcases p792_3 (m.d 1 3) (by simp) with h814 | h814
                        · linarith only [h1, h814, hlam]
                        · rcases p792_3 (m.d 1 4) (by simp) with h816 | h816
                          · linarith only [h2, h816, hlam]
                          · linarith only [h788, h816, hlam]
                    · linarith only [h811, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h0, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h4, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h322, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h431, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h1, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h700, hc12, hlam, hphi, ht23, ht34, ht45, p792_1, u5elo1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h571, hlam, p792_1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h700, hlam, p792_1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h2, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p792_1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h571, h789, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p792_1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h571, h789, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h3, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p792_1, u5elo1]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h4, h700, h790, hc12, hlam, hphi, ht23, ht34, ht45, p792_1, u5elo2]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [h788, hlam, p792_0]
                  · have p792_0 := h792c.1
                    have p792_1 := h792c.2.1
                    have p792_2 := h792c.2.2.1
                    have p792_3 := h792c.2.2.2
                    linarith only [hlam, p792_0]
                · linarith only [h4, h571, h791, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h4, h790, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h842 | h842
              · linarith only [h4, h700, h789, h842, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h4, h842, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h845 | h845
            · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
              · rcases m.htr 3 4 5 (by decide) (by decide) with h847 | h847
                · linarith only [h322, h788, h845, h847, hc12, hc23, hlam, hphi]
                · linarith only [h4, h571, h847, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h4, h846, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h851 | h851
              · linarith only [h4, h700, h845, h851, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h4, h851, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_15_H_I_L_0_x0_x0_x0_x0_x0 m hb1 hb5 h0 h1 h2 h3 h4
  · exact r1l7_21_15_H_I_L_0_x0_x0_x0_x0_x1 m hb1 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_15_H_I_L_0_x0_x0_x0_x0 m hb1 hb5 h0 h1 h2 h3
  · exact r1l7_21_15_H_I_L_0_x0_x0_x0_x1 m hb1 hb5 h0 h1 h2 h3

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h855 | h855
  · rcases m.htr 1 2 3 (by decide) (by decide) with h856 | h856
    · rcases m.htr 1 2 4 (by decide) (by decide) with h857 | h857
      · linarith only [h0, h2, h857, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h859 | h859
        · rcases m.htr 1 3 4 (by decide) (by decide) with h860 | h860
          · linarith only [h1, h2, h860, hlam]
          · linarith only [h0, h2, h856, h860, hc23, hc34, hlam, hphi]
        · linarith only [h856, h859, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h864 | h864
      · linarith only [h0, h2, h864, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h866 | h866
        · rcases m.htr 1 3 4 (by decide) (by decide) with h867 | h867
          · linarith only [h1, h2, h867, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h869 | h869
            · rcases m.htr 1 4 5 (by decide) (by decide) with h870 | h870
              · rcases m.htr 2 3 4 (by decide) (by decide) with h871 | h871
                · linarith only [h1, h2, h856, h866, h867, h871, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h874 | h874
                    · rcases h1bigk with h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h866, h873, h874, hc01, hc45, hlam, hphi, ht0b, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h2, h856, h864, h866, h871, h873, h874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h2, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h2, h864, h866, h871, h873, h874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h0, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h856, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h864, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h0, h2, h864, h866, h871, h873, h874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h1, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h1, h2, h864, h871, hc12, hc34, hlam, hphi, ht23, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h867, hlam, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h1, h2, h864, h866, h871, h873, h874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h864, h871, hc01, hc34, hlam, hphi, ht12, ht23, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h864, h866, h871, h873, h874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h856, h864, h866, h871, h873, h874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        rcases p875_3 (m.d 0 1) (by simp) with h895 | h895
                        · linarith only [h2, h895, hlam]
                        · linarith only [h855, h895, hlam]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h855, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h866, hlam, p875_1]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h869, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [h870, hlam, p875_0]
                      · have p875_0 := h875c.1
                        have p875_1 := h875c.2.1
                        have p875_2 := h875c.2.2.1
                        have p875_3 := h875c.2.2.2
                        linarith only [hlam, p875_0]
                    · linarith only [h871, h874, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1, h2, h856, h864, h869, h871, h873, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h2, h870, hc13, hc45, hlam, hphi, ht34]
            · linarith only [h856, h866, h869, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h907 | h907
          · linarith only [h1, h2, h907, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
            · rcases m.htr 1 4 5 (by decide) (by decide) with h910 | h910
              · rcases m.htr 2 3 4 (by decide) (by decide) with h911 | h911
                · linarith only [h1, h2, h907, h909, h911, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h913 | h913
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h914 | h914
                    · rcases h1bigk with h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c | h915c
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h2, h864, h909, h914, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h2, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h2, h864, h866, hc12, hc24, hlam, hphi, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h0, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h856, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h864, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h866, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h1, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h1, h2, h864, hc12, hc24, hlam, hphi, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h907, hlam, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h1, h2, h866, h907, hc12, hc34, hlam, hphi, ht23, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h907, hc01, hc34, hlam, hphi, ht12, ht23, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h907, hc12, hc34, hlam, hphi, ht23, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h856, h907, hc12, hc34, hlam, hphi, ht23, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h866, h907, hc12, hc34, hlam, hphi, ht23, p915_1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h855, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p915_1, u5elo1]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h909, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [h910, hlam, p915_0]
                      · have p915_0 := h915c.1
                        have p915_1 := h915c.2.1
                        have p915_2 := h915c.2.2.1
                        have p915_3 := h915c.2.2.2
                        linarith only [hlam, p915_0]
                    · linarith only [h1, h2, h864, h909, h911, h914, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                  · linarith only [h1, h2, h909, h913, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h2, h910, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h944 | h944
              · rcases m.htr 2 3 4 (by decide) (by decide) with h945 | h945
                · linarith only [h2, h855, h856, h907, h909, h945, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h947 | h947
                  · linarith only [h856, h909, h945, h947, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h856, h947, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h2, h855, h856, h909, h944, hc12, hc45, hlam, hphi, ht23, ht34]
  · linarith only [h0, h855, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1bigk := hb1.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_15_H_I_L_0_x0_x0_x0 m hb1 hb5 h0 h1 h2
  · exact r1l7_21_15_H_I_L_0_x0_x0_x1 m hb1 hb5 h0 h1 h2

end R2N4
