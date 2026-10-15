import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S4
import Jsp000404.R1LeavesN7_41S5
import Jsp000404.R1LeavesN7_41S6
import Jsp000404.R1LeavesN7_41S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h2261 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2601 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h3002 | h3002
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3003 | h3003
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3004 | h3004
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3005 | h3005
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3006 | h3006
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3007 | h3007
            · rcases h5bigk with h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h0, hlam, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h1741, hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p3008_1, u1elo4]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h2261, hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3008_1, u1elo4]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h2601, hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h3002, hc35, hlam, hphi, ht01, ht0b, ht5b, p3008_1, u1elo2]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h2261, h3002, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3008_1, u1elo2]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h2261, h3004, h3006, h3007, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h2261, h3004, h3006, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h3002, hlam, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h3005, hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [hlam, p3008_0]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h2261, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h3003, hlam, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h3006, hlam, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [h3007, hlam, p3008_1]
              · have p3008_0 := h3008c.1
                have p3008_1 := h3008c.2.1
                have p3008_2 := h3008c.2.2.1
                have p3008_3 := h3008c.2.2.2
                linarith only [hlam, p3008_0]
            · rcases h5bigk with h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c | h3034c
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h0, hlam, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h1741, hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p3034_1, u1elo4]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h2261, hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3034_1, u1elo4]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h2601, hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3002, hc35, hlam, hphi, ht01, ht0b, ht5b, p3034_1, u1elo2]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3002, h3007, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3034_1, u1elo2]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h0, h3004, h3006, hc01, hc23, hlam, hphi, ht12, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h0, h3004, h3006, hc01, hc23, hlam, hphi, ht12, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                rcases p3034_3 (m.d 0 5) (by simp) with h3048 | h3048
                · linarith only [h1741, h3048, hlam]
                · linarith only [h0, h3004, h3006, h3048, hc01, hc23, hlam, hphi, ht12, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3004, h3006, h3007, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3002, hlam, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3005, hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3007, hlam, p3034_0]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3003, hlam, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3006, hlam, p3034_1]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [h3003, hc35, hlam, hphi, ht01, ht0b, ht5b, p3034_1, u1elo3]
              · have p3034_0 := h3034c.1
                have p3034_1 := h3034c.2.1
                have p3034_2 := h3034c.2.2.1
                have p3034_3 := h3034c.2.2.2
                linarith only [hlam, p3034_0]
          · linarith only [h0, h2601, h3003, h3006, hc01, hlam, hphi, u1elo3]
        · linarith only [h3002, h3004, h3005, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3064 | h3064
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3065 | h3065
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3066 | h3066
            · rcases h5bigk with h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c | h3067c
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h0, hlam, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h1741, hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p3067_1, u1elo4]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2261, hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3067_1, u1elo4]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2601, hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2261, h3002, h3066, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3067_1, u1elo2]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2261, h3002, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3067_1, u1elo2]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2261, h3004, h3064, h3066, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2261, h3004, h3064, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h3002, hlam, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h3064, hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [hlam, p3067_0]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h2261, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h3003, hlam, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h3065, hlam, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [h3066, hlam, p3067_1]
              · have p3067_0 := h3067c.1
                have p3067_1 := h3067c.2.1
                have p3067_2 := h3067c.2.2.1
                have p3067_3 := h3067c.2.2.2
                linarith only [hlam, p3067_0]
            · linarith only [h2601, h3003, h3004, h3064, h3066, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
          · linarith only [h0, h2601, h3003, h3004, h3064, h3065, hc01, hlam, hphi, u1elo3]
        · linarith only [h0, h2601, h3002, h3064, hc01, hlam, hphi, u1elo2]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3096 | h3096
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3097 | h3097
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3098 | h3098
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3099 | h3099
            · linarith only [h0, h3003, h3096, h3099, hc01, hc23, hlam, hphi, ht12]
            · rcases h5bigk with h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c | h3101c
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hlam, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h1741, hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p3101_1, u1elo4]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h2261, hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3101_1, u1elo4]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h2601, hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3003, h3098, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3003, hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                rcases p3101_3 (m.d 0 5) (by simp) with h3115 | h3115
                · linarith only [h1741, h3115, hlam]
                · linarith only [h0, h3096, h3098, h3115, hc01, hc23, hlam, hphi, ht12, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3003, h3096, h3098, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3002, hlam, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3097, hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3099, hlam, p3101_0]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3098, hlam, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [h3096, h3098, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3101_1]
              · have p3101_0 := h3101c.1
                have p3101_1 := h3101c.2.1
                have p3101_2 := h3101c.2.2.1
                have p3101_3 := h3101c.2.2.2
                linarith only [hlam, p3101_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3129 | h3129
            · linarith only [h1741, h3096, h3098, h3129, hc02, hc23, hlam, hphi]
            · rcases h5bigk with h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c | h3131c
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, hlam, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h1741, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, h3129, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3131_1, u1elo4]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h2261, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3131_1, u1elo4]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h2601, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3002, h3129, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3131_1, u1elo2]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3003, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, h3098, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3098, h3129, hc34, hc45, hlam, hphi, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3098, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3002, hlam, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3097, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3129, hlam, p3131_0]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h1741, hc02, hc45, hlam, hphi, ht23, ht34, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [h3129, hc34, hc45, hlam, hphi, p3131_1]
              · have p3131_0 := h3131c.1
                have p3131_1 := h3131c.2.1
                have p3131_2 := h3131c.2.2.1
                have p3131_3 := h3131c.2.2.2
                linarith only [hlam, p3131_0]
        · linarith only [h3002, h3096, h3097, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3158 | h3158
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3159 | h3159
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3160 | h3160
            · linarith only [h0, h3002, h3003, h3160, hc01, hlam, hphi, u1elo2]
            · linarith only [h3096, h3158, h3159, h3160, hlam]
          · linarith only [h3096, h3158, h3159, hlam]
        · linarith only [h0, h2601, h3002, h3158, hc01, hlam, hphi, u1elo2]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3165 | h3165
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3166 | h3166
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3167 | h3167
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3168 | h3168
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3169 | h3169
            · rcases h5bigk with h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c | h3170c
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, hlam, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h1741, hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, h3002, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h2261, hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3170_1, u1elo4]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h2601, hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h3002, hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h2261, h3165, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3170_1, u1elo3]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, h3002, h3167, hc01, hc23, hlam, hphi, ht12, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h2261, h3166, h3168, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h3167, hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [hlam, p3170_0]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h2261, h3166, h3169, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h3165, hlam, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h3168, hlam, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [h3169, hlam, p3170_1]
              · have p3170_0 := h3170c.1
                have p3170_1 := h3170c.2.1
                have p3170_2 := h3170c.2.2.1
                have p3170_3 := h3170c.2.2.2
                linarith only [hlam, p3170_0]
            · linarith only [h0, h3002, h3165, h3169, hc01, hlam, hphi, u1elo3]
          · linarith only [h0, h2601, h3165, h3168, hc01, hlam, hphi, u1elo3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3198 | h3198
          · linarith only [h3166, h3167, h3198, hlam]
          · linarith only [h0, h2601, h3165, h3198, hc01, hlam, hphi, u1elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3201 | h3201
        · linarith only [h3002, h3166, h3201, hc13, hc34, hlam, hphi]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3203 | h3203
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3204 | h3204
            · rcases h5bigk with h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h0, hlam, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h1741, hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h2261, h3165, h3201, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3205_1, u1elo3]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h2261, hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h1741, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3205_1, u1elo4]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h2601, hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h3002, hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h3165, hc45, hlam, hphi, ht01, ht0b, ht5b, p3205_1, u1elo3]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h3201, hlam, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h2261, h3203, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h0, h3204, hc01, hc34, hlam, hphi, ht12, ht23, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h0, h3204, hc01, hc34, hlam, hphi, ht12, ht23, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h1741, h3204, hc02, hc34, hlam, hphi, ht23, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [hlam, p3205_0]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h2261, h3204, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h3165, hlam, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h3203, hlam, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [h3204, hlam, p3205_1]
              · have p3205_0 := h3205c.1
                have p3205_1 := h3205c.2.1
                have p3205_2 := h3205c.2.2.1
                have p3205_3 := h3205c.2.2.2
                linarith only [hlam, p3205_0]
            · linarith only [h3165, h3166, h3204, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · linarith only [h0, h2601, h3165, h3203, hc01, hlam, hphi, u1elo3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3233 | h3233
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3234 | h3234
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3235 | h3235
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3236 | h3236
            · linarith only [h0, h3165, h3233, h3236, hc01, hc23, hlam, hphi, ht12]
            · rcases h5bigk with h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c | h3238c
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hlam, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h1741, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, h3002, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h2261, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3238_1, u1elo4]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h2601, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3002, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3165, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3002, h3234, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3165, h3233, h3235, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3234, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3236, hlam, p3238_0]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3235, hlam, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [h3002, hc13, hc45, hlam, hphi, ht34, p3238_1]
              · have p3238_0 := h3238c.1
                have p3238_1 := h3238c.2.1
                have p3238_2 := h3238c.2.2.1
                have p3238_3 := h3238c.2.2.2
                linarith only [hlam, p3238_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3264 | h3264
            · linarith only [h3233, h3235, h3264, hlam]
            · rcases h5bigk with h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c | h3266c
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, hlam, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h1741, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, h3002, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h2261, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3266_1, u1elo4]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h2601, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h3002, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h3165, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, h3235, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, h3235, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, h3002, h3235, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h3235, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h3234, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h3264, hlam, p3266_0]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h1741, hc02, hc45, hlam, hphi, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [h0, h3002, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3266_1]
              · have p3266_0 := h3266c.1
                have p3266_1 := h3266c.2.1
                have p3266_2 := h3266c.2.2.1
                have p3266_3 := h3266c.2.2.2
                linarith only [hlam, p3266_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3292 | h3292
          · linarith only [h0, h3165, h3233, h3234, h3292, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3294 | h3294
            · linarith only [h3233, h3234, h3292, h3294, hlam]
            · rcases h5bigk with h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, hlam, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h1741, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3234, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h2261, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3296_1, u1elo4]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h2601, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3002, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3165, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3234, hlam, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3292, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, h3294, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, h2601, h3294, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3294, hlam, p3296_0]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h0, h2601, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [h3002, hc13, hc45, hlam, hphi, ht34, p3296_1]
              · have p3296_0 := h3296c.1
                have p3296_1 := h3296c.2.1
                have p3296_2 := h3296c.2.2.1
                have p3296_3 := h3296c.2.2.2
                linarith only [hlam, p3296_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3322 | h3322
        · linarith only [h0, h3002, h3233, h3322, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3324 | h3324
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3325 | h3325
            · rcases h5bigk with h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c | h3326c
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, hlam, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h1741, hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h3322, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h2261, hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3326_1, u1elo4]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h2601, hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h3002, hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h3165, hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h3322, hlam, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, h3165, h3324, hc01, hc24, hlam, hphi, ht12, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, h3325, hc01, hc34, hlam, hphi, ht12, ht23, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, h3325, hc01, hc34, hlam, hphi, ht12, ht23, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h1741, h3325, hc02, hc34, hlam, hphi, ht23, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [hlam, p3326_0]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, h3165, h3325, hc01, hc34, hlam, hphi, ht12, ht23, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, h3324, hc01, hc25, hlam, hphi, ht12, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h3324, hlam, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [h3325, hlam, p3326_1]
              · have p3326_0 := h3326c.1
                have p3326_1 := h3326c.2.1
                have p3326_2 := h3326c.2.2.1
                have p3326_3 := h3326c.2.2.2
                linarith only [hlam, p3326_0]
            · linarith only [h3233, h3324, h3325, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3353 | h3353
            · rcases h5bigk with h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c | h3354c
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hlam, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h1741, hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p3354_1, u1elo4]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h2261, hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3354_1, u1elo4]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h2601, hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h3002, hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h3165, hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, h3324, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h3322, hlam, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h3324, hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h1741, hc02, hc35, hlam, hphi, ht23, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [hlam, p3354_0]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h3324, h3353, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h0, h2601, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [h3353, hlam, p3354_1]
              · have p3354_0 := h3354c.1
                have p3354_1 := h3354c.2.1
                have p3354_2 := h3354c.2.2.1
                have p3354_3 := h3354c.2.2.2
                linarith only [hlam, p3354_0]
            · rcases h5bigk with h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c | h3380c
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, hlam, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h1741, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo4]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h2261, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3380_1, u1elo4]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h2601, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h3002, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h3165, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h3322, hlam, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h3324, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, h3353, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, h3353, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h1741, h3353, hc02, hc45, hlam, hphi, ht23, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h3353, hlam, p3380_0]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h0, h2601, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [h3002, hc13, hc45, hlam, hphi, ht34, p3380_1]
              · have p3380_0 := h3380c.1
                have p3380_1 := h3380c.2.1
                have p3380_2 := h3380c.2.2.1
                have p3380_3 := h3380c.2.2.2
                linarith only [hlam, p3380_0]

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h2261 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h2601 | h2601
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x1_x0 m hb1 hb2 hb5 h0 h1741 h2261 h2601
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x1_x1 m hb1 hb2 hb5 h0 h1741 h2261 h2601

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2261 | h2261
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x0 m hb1 hb2 hb5 h0 h1741 h2261
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x1 m hb1 hb2 hb5 h0 h1741 h2261

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1741 | h1741
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1_x0 m hb1 hb2 hb5 h0 h1741
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1_x1 m hb1 hb2 hb5 h0 h1741

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0 m hb1 hb2 hb5 h0
  · exact r1l7_11_12_25_L_0_L_I_H_I_x1 m hb1 hb2 hb5 h0

end R2N4
