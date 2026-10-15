import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S5

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_23_L_0_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h801 | h801
  · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
    · rcases m.htr 0 3 5 (by decide) (by decide) with h803 | h803
      · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
        · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
          · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
            · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
              · rcases m.htr 3 4 5 (by decide) (by decide) with h808 | h808
                · linarith only [h804, h806, h808, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases h3bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h0, hlam, p810_1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h807, h808, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h0, h804, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h0, h804, h808, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h804, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h804, h807, h808, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h804, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h804, h808, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h801, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h804, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h801, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h804, h808, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h802, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h0, hc03, hc34, hlam, hphi, p810_1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h806, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h808, hlam, p810_1]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h803, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h805, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h807, hlam, p810_0]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [h0, h803, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1, u1elo2]
                  · have p810_0 := h810c.1
                    have p810_1 := h810c.2.1
                    have p810_2 := h810c.2.2.1
                    have p810_3 := h810c.2.2.2
                    linarith only [hlam, p810_0]
              · linarith only [h0, h803, h804, h806, h807, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h837 | h837
              · linarith only [h0, h802, h804, h806, h837, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h839 | h839
                · rcases h3bigk with h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h0, hlam, p840_1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h0, h804, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h0, h804, h837, h839, hc25, hlam, hphi, ht01, ht0b, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h0, h804, h837, hc25, hlam, hphi, ht01, ht0b, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h804, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h804, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h804, h837, h839, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h804, h837, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h801, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h804, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h806, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h837, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h802, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h802, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p840_1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h0, h802, h804, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h0, h802, h804, h837, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p840_1, u1elo1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h803, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h805, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [hc23, hc35, hlam, hphi, p840_1]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [h839, hlam, p840_0]
                  · have p840_0 := h840c.1
                    have p840_1 := h840c.2.1
                    have p840_2 := h840c.2.2.1
                    have p840_3 := h840c.2.2.2
                    linarith only [hlam, p840_0]
                · rcases h3bigk with h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h0, hlam, p866_1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h0, h804, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h0, h804, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h0, h804, hc35, hlam, hphi, ht01, ht0b, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h804, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h804, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h804, h806, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h804, h806, h839, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h801, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h804, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h806, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h837, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h802, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h803, h839, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p866_1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h803, h839, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p866_1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h839, hlam, p866_1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h803, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h805, hlam, p866_0]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h0, h803, h804, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [h0, h803, h804, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p866_1, u1elo1]
                  · have p866_0 := h866c.1
                    have p866_1 := h866c.2.1
                    have p866_2 := h866c.2.2.1
                    have p866_3 := h866c.2.2.2
                    linarith only [hlam, p866_0]
          · linarith only [h0, h803, h805, hlam]
        · linarith only [h0, h801, h804, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h894 | h894
        · rcases m.htr 1 3 5 (by decide) (by decide) with h895 | h895
          · linarith only [h0, h803, h895, hc01, hlam, hphi, u1elo2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h897 | h897
            · rcases m.htr 2 3 5 (by decide) (by decide) with h898 | h898
              · linarith only [h0, h895, h898, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h900 | h900
                · linarith only [h894, h897, h900, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases h3bigk with h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h0, hlam, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h0, h895, h900, hc23, hc45, hlam, hphi, ht34, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h0, h895, h900, hc34, hc45, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h803, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h895, h900, hc03, hc45, hlam, hphi, ht34, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h895, h897, h900, hc34, hc45, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h895, h900, hc34, hc45, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h895, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h801, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h894, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h0, h801, h895, h900, hc34, hc45, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h898, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h802, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h0, hc03, hc34, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h897, hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [hlam, p902_0]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h900, hlam, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h802, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h0, h900, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h897, h900, hc34, hc45, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [h900, hc34, hc45, hlam, hphi, p902_1]
                  · have p902_0 := h902c.1
                    have p902_1 := h902c.2.1
                    have p902_2 := h902c.2.2.1
                    have p902_3 := h902c.2.2.2
                    linarith only [hlam, p902_0]
            · linarith only [h802, h803, h897, hc23, hc35, hlam, hphi]
        · linarith only [h0, h801, h894, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h930 | h930
      · rcases m.htr 1 2 3 (by decide) (by decide) with h931 | h931
        · rcases m.htr 1 3 5 (by decide) (by decide) with h932 | h932
          · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
            · linarith only [h802, h931, h933, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h935 | h935
              · rcases m.htr 3 4 5 (by decide) (by decide) with h936 | h936
                · rcases h3bigk with h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, hlam, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h935, h936, hc03, hc45, hlam, hphi, ht0b, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h802, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h802, h936, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p937_1, u1elo2]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h931, h935, h936, hc45, hlam, hphi, ht01, ht0b, ht5b, p937_1, u1elo1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h802, h931, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p937_1, u1elo1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h931, h936, hc45, hlam, hphi, ht01, ht0b, ht5b, p937_1, u1elo1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h801, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h931, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h933, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h801, h802, h936, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hc03, hc34, hlam, hphi, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hc13, hc34, hlam, hphi, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h935, h936, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    rcases p937_3 (m.d 0 3) (by simp) with h957 | h957
                    · linarith only [h802, h957, hlam]
                    · linarith only [h930, h957, hlam]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h930, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h932, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h935, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h936, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                · linarith only [h801, h802, h935, h936, hlam]
              · linarith only [h802, h930, h935, hc23, hc34, hlam, hphi]
          · linarith only [h0, h930, h932, hlam]
        · linarith only [h0, h801, h931, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h969 | h969
        · rcases m.htr 1 3 5 (by decide) (by decide) with h970 | h970
          · linarith only [h0, h930, h970, hc01, hlam, hphi, u1elo2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
            · linarith only [h801, h802, h972, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h974 | h974
              · linarith only [h801, h802, h970, h974, hc13, hc34, hlam, hphi]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h976 | h976
                · rcases h3bigk with h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c | h977c
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h0, hlam, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h0, h970, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p977_1, u1elo4]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h802, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h930, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h970, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p977_1, u1elo4]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h970, h976, hc23, hc34, hlam, hphi, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h970, h976, hlam, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h970, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h801, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h969, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h972, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h974, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hc13, hc34, hlam, hphi, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h0, h930, hc01, hc34, hlam, hphi, ht12, ht23, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hc23, hc35, hlam, hphi, p977_1]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [h976, hlam, p977_0]
                  · have p977_0 := h977c.1
                    have p977_1 := h977c.2.1
                    have p977_2 := h977c.2.2.1
                    have p977_3 := h977c.2.2.2
                    linarith only [hlam, p977_0]
                · rcases h3bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h0, hlam, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h0, h969, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1, u1elo1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h802, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h930, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h969, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1, u1elo1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h969, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1, u1elo1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h802, h970, h976, hc04, hc45, hlam, hphi, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h970, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h801, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h969, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h972, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h974, hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h976, hc13, hc45, hlam, hphi, ht34, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h976, hc23, hc45, hlam, hphi, ht34, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [hlam, p1003_0]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h976, hlam, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h0, h976, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h0, h976, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h976, hc23, hc45, hlam, hphi, ht34, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [h976, hc34, hc45, hlam, hphi, p1003_1]
                  · have p1003_0 := h1003c.1
                    have p1003_1 := h1003c.2.1
                    have p1003_2 := h1003c.2.2.1
                    have p1003_3 := h1003c.2.2.2
                    linarith only [hlam, p1003_0]
        · linarith only [h0, h801, h969, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1030 | h1030
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1031 | h1031
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1033 | h1033
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1034 | h1034
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1035 | h1035
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1036 | h1036
                · linarith only [h1030, h1032, h1036, h801, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases h3bigk with h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h0, hlam, p1038_1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h801, hlam, p1038_1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, h801, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, h801, hc35, hlam, hphi, ht01, ht0b, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1038_1, u1elo2]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, h801, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, h1036, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1031, h1036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1032, h1036, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1038_1, u1elo1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1030, hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1031, h1036, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1038_1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1034, hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1036, hlam, p1038_1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1031, hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1033, hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1035, hlam, p1038_0]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [h1031, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1038_1]
                  · have p1038_0 := h1038c.1
                    have p1038_1 := h1038c.2.1
                    have p1038_2 := h1038c.2.2.1
                    have p1038_3 := h1038c.2.2.2
                    linarith only [hlam, p1038_0]
              · linarith only [h1031, h1035, h801, hlam]
            · linarith only [h1030, h1034, h801, hlam]
          · linarith only [h1031, h1032, h1033, h801, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1067 | h1067
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1068 | h1068
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1069 | h1069
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1070 | h1070
                · rcases h3bigk with h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h0, hlam, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h801, hlam, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1070, hc03, hc45, hlam, hphi, ht0b, ht5b, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1071_1, u1elo2]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1071_1, u1elo2]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1032, hlam, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1070, hc45, hlam, hphi, ht01, ht0b, ht5b, p1071_1, u1elo2]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1070, hc45, hlam, hphi, ht01, ht0b, ht5b, p1071_1, u1elo2]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1030, h1070, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1070, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    rcases p1071_3 (m.d 0 3) (by simp) with h1086 | h1086
                    · linarith only [h1086, h801, hlam]
                    · linarith only [h1031, h1086, hlam]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1030, hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h0, h1030, hlam, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1068, hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1030, h1070, hc03, hc45, hlam, hphi, ht0b, ht5b, p1071_1]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1031, hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1067, hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1069, hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [h1070, hlam, p1071_0]
                  · have p1071_0 := h1071c.1
                    have p1071_1 := h1071c.2.1
                    have p1071_2 := h1071c.2.2.1
                    have p1071_3 := h1071c.2.2.2
                    linarith only [hlam, p1071_0]
                · rcases h3bigk with h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h0, hlam, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h801, hlam, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1, u1elo2]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1099_1, u1elo2]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1099_1, u1elo2]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1032, hlam, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1, u1elo2]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1070, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1099_1, u1elo2]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1031, h1070, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    rcases p1099_3 (m.d 0 3) (by simp) with h1113 | h1113
                    · linarith only [h1113, h801, hlam]
                    · linarith only [h1030, h1113, hlam]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    rcases p1099_3 (m.d 0 3) (by simp) with h1116 | h1116
                    · linarith only [h1116, h801, hlam]
                    · linarith only [h1031, h1116, hlam]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1030, hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h0, h1031, h1070, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1068, hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1070, hlam, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1031, hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1067, hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1069, hlam, p1099_0]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [h1031, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1099_1]
                  · have p1099_0 := h1099c.1
                    have p1099_1 := h1099c.2.1
                    have p1099_2 := h1099c.2.2.1
                    have p1099_3 := h1099c.2.2.2
                    linarith only [hlam, p1099_0]
              · linarith only [h0, h1031, h1032, h1069, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1030, h1032, h1068, hlam]
          · linarith only [h0, h1031, h1067, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1132 | h1132
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1133 | h1133
          · linarith only [h1030, h1031, h1133, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1135 | h1135
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1136 | h1136
              · linarith only [h1132, h1133, h1136, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1138 | h1138
                · linarith only [h1030, h1132, h1138, h801, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases h3bigk with h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h0, hlam, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h801, hlam, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1132, h801, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1140_1, u1elo1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1031, hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1140_1, u1elo2]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1133, h1138, hc23, hc45, hlam, hphi, ht34, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1133, h1138, hc34, hc45, hlam, hphi, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1133, hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1132, hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1132, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1140_1, u1elo1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1136, hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1030, hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1030, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1135, hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [hlam, p1140_0]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1138, hlam, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1138, hc03, hc45, hlam, hphi, ht34, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1138, hc13, hc45, hlam, hphi, ht34, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1138, hc23, hc45, hlam, hphi, ht34, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [h1138, hc34, hc45, hlam, hphi, p1140_1]
                  · have p1140_0 := h1140c.1
                    have p1140_1 := h1140c.2.1
                    have p1140_2 := h1140c.2.2.1
                    have p1140_3 := h1140c.2.2.2
                    linarith only [hlam, p1140_0]
            · linarith only [h0, h1030, h1135, h801, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1167 | h1167
          · linarith only [h1030, h1031, h1167, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
              · linarith only [h0, h1167, h1170, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1172 | h1172
                · linarith only [h0, h1030, h1132, h1170, h1172, hlam]
                · rcases h3bigk with h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h0, hlam, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h801, hlam, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h0, h1132, h1170, h1172, hc34, hc45, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1031, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1132, h1170, h1172, hc03, hc45, hlam, hphi, ht34, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1132, hlam, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1132, h1170, h1172, hc34, hc45, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1167, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1030, h1170, h1172, hc34, hc45, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1170, h1172, hc13, hc45, hlam, hphi, ht34, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1170, h1172, hc34, hc45, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1170, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1030, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h0, h1030, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1169, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1172, hlam, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1172, hc03, hc45, hlam, hphi, ht34, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1172, hc13, hc45, hlam, hphi, ht34, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1132, h1172, hc12, hc45, hlam, hphi, ht23, ht34, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1172, hc34, hc45, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
            · linarith only [h0, h1030, h1132, h1169, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1201 | h1201
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1202 | h1202
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1203 | h1203
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1204 | h1204
            · linarith only [h1030, h1202, h1204, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1206 | h1206
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1207 | h1207
                · rcases h3bigk with h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h0, hlam, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h801, hlam, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1030, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h0, h1202, h1207, hc45, hlam, hphi, ht01, ht0b, ht5b, p1208_1, u1elo1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1202, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1208_1, u1elo1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1202, h801, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1208_1, u1elo1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1202, h1204, h801, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1208_1, u1elo1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1202, h1207, hc45, hlam, hphi, ht01, ht0b, ht5b, p1208_1, u1elo1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1201, h1207, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1202, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1204, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1202, h1207, hc45, hlam, hphi, ht01, ht0b, ht5b, p1208_1, u1elo1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1201, h1207, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hc13, hc34, hlam, hphi, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    rcases p1208_3 (m.d 0 3) (by simp) with h1228 | h1228
                    · linarith only [h1030, h1228, hlam]
                    · linarith only [h1201, h1228, hlam]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1201, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1203, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1206, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1207, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                · linarith only [h1204, h1207, h801, hc02, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h0, h1201, h1206, h801, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · linarith only [h1201, h1202, h1203, h801, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1239 | h1239
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1240 | h1240
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1241 | h1241
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1242 | h1242
                · rcases h3bigk with h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h0, hlam, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h801, hlam, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1030, hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1030, h1240, h1242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1243_1, u1elo2]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1202, hlam, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1030, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p1243_1, u1elo2]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1242, hc45, hlam, hphi, ht01, ht0b, ht5b, p1243_1, u1elo2]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1201, h1242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1030, h1201, h1242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    rcases p1243_3 (m.d 0 3) (by simp) with h1258 | h1258
                    · linarith only [h1258, h801, hlam]
                    · linarith only [h1201, h1258, hlam]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1201, h1240, h1242, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h0, h1240, hc01, hc23, hlam, hphi, ht12, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1240, hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1240, h1242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1243_1]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1201, hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1239, hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1241, hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [h1242, hlam, p1243_0]
                  · have p1243_0 := h1243c.1
                    have p1243_1 := h1243c.2.1
                    have p1243_2 := h1243c.2.2.1
                    have p1243_3 := h1243c.2.2.2
                    linarith only [hlam, p1243_0]
                · linarith only [h1030, h1201, h1242, hlam]
              · linarith only [h1030, h1201, h1241, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1273 | h1273
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                · rcases h3bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h0, hlam, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h801, hlam, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1030, hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h0, h1202, h1240, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1202, h1240, hc03, hc34, hlam, hphi, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1202, hlam, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1202, h1240, hlam, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1202, h1240, h1274, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1201, h1240, h1274, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1240, hc13, hc34, hlam, hphi, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1240, hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1240, h1274, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1201, h1274, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1202, hc12, hc34, hlam, hphi, ht23, p1275_1]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    rcases p1275_3 (m.d 0 3) (by simp) with h1295 | h1295
                    · linarith only [h1030, h1295, hlam]
                    · linarith only [h1201, h1295, hlam]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1201, hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1239, hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1273, hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [h1274, hlam, p1275_0]
                  · have p1275_0 := h1275c.1
                    have p1275_1 := h1275c.2.1
                    have p1275_2 := h1275c.2.2.1
                    have p1275_3 := h1275c.2.2.2
                    linarith only [hlam, p1275_0]
                · linarith only [h0, h1202, h1240, h1274, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h1201, h1202, h1273, hlam]
          · linarith only [h0, h1201, h1239, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1306 | h1306
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1307 | h1307
          · linarith only [h0, h1201, h1307, hc01, hlam, hphi, u1elo2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1309 | h1309
            · linarith only [h1030, h1306, h1309, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1311 | h1311
              · linarith only [h0, h1307, h1311, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1313 | h1313
                · rcases h3bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, hlam, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h801, hlam, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1030, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1201, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, p1314_1, u1elo2]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1307, hc23, hc35, hlam, hphi, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1307, h1313, hlam, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1307, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1306, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1309, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1311, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hc13, hc34, hlam, hphi, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hc23, hc34, hlam, hphi, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, h1201, hc01, hc34, hlam, hphi, ht12, ht23, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h801, hc02, hc35, hlam, hphi, ht23, p1314_1]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [h1313, hlam, p1314_0]
                  · have p1314_0 := h1314c.1
                    have p1314_1 := h1314c.2.1
                    have p1314_2 := h1314c.2.2.1
                    have p1314_3 := h1314c.2.2.2
                    linarith only [hlam, p1314_0]
                · linarith only [h1309, h1313, h801, hc02, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1341 | h1341
          · linarith only [h0, h1201, h1341, hc01, hlam, hphi, u1elo2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1343 | h1343
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1344 | h1344
              · linarith only [h0, h1341, h1344, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h1030, h1343, h1344, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
              · linarith only [h0, h1201, h1343, h1347, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1349 | h1349
                · rcases h3bigk with h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, hlam, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h801, hlam, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1030, hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1201, hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, p1350_1, u1elo2]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1306, hlam, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1306, h1347, h1349, hlam, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1341, hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, h1347, h1349, hc01, hc34, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1347, h1349, hc13, hc34, hlam, hphi, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1343, hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1347, hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1306, hc12, hc34, hlam, hphi, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, h1201, hc01, hc34, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h0, h1306, hc01, hc35, hlam, hphi, ht12, ht23, p1350_1]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [h1349, hlam, p1350_0]
                  · have p1350_0 := h1350c.1
                    have p1350_1 := h1350c.2.1
                    have p1350_2 := h1350c.2.2.1
                    have p1350_3 := h1350c.2.2.2
                    linarith only [hlam, p1350_0]
                · linarith only [h0, h1306, h1343, h1349, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem r1l7_11_23_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_23_L_0_H_I_x0 m hb1 hb3 h0
  · exact r1l7_11_23_L_0_H_I_x1 m hb1 hb3 h0

end R2N4
