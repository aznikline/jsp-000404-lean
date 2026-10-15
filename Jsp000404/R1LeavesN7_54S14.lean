import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S12
import Jsp000404.R1LeavesN7_54S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1255 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1685 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h1995 | h1995
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1996 | h1996
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1997 | h1997
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1998 | h1998
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1999 | h1999
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2000 | h2000
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2001 | h2001
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2002 | h2002
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2003 | h2003
                  · rcases h1bigk with h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c | h2004c
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h0, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1255, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1521, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1685, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1255, hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1521, hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1685, hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1995, hlam, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1521, h1995, hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1685, h1995, hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1996, hlam, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1998, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1685, h1995, h1998, hc01, hc12, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hc01, hc15, hlam, hphi, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1997, hlam, p2004_1]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h1999, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [h2000, hlam, p2004_0]
                    · have p2004_0 := h2004c.1
                      have p2004_1 := h2004c.2.1
                      have p2004_2 := h2004c.2.2.1
                      have p2004_3 := h2004c.2.2.2
                      linarith only [hlam, p2004_0]
                  · rcases h1bigk with h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c | h2030c
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h0, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1255, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1521, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1685, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1255, hc01, hc12, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1521, hc01, hc12, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h2000, h2003, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1995, hlam, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1521, h1995, hc01, hc12, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1685, h1995, hc01, hc12, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1996, hlam, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1998, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1685, h1995, h1998, hc01, hc12, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hc01, hc15, hlam, hphi, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1997, hlam, p2030_1]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h1999, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [h2000, hlam, p2030_0]
                    · have p2030_0 := h2030c.1
                      have p2030_1 := h2030c.2.1
                      have p2030_2 := h2030c.2.2.1
                      have p2030_3 := h2030c.2.2.2
                      linarith only [hlam, p2030_0]
                · linarith only [h1999, h2001, h2002, hc34, hlam, hphi, ht45, u5elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2057 | h2057
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2058 | h2058
                  · rcases h1bigk with h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h0, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1255, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1521, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1685, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1255, hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1521, hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1685, hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1995, hlam, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1521, h1995, hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1685, h1995, hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1996, hlam, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1998, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1685, h1995, h1998, hc01, hc12, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hc01, hc15, hlam, hphi, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1997, hlam, p2059_1]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h1999, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [h2000, hlam, p2059_0]
                    · have p2059_0 := h2059c.1
                      have p2059_1 := h2059c.2.1
                      have p2059_2 := h2059c.2.2.1
                      have p2059_3 := h2059c.2.2.2
                      linarith only [hlam, p2059_0]
                  · linarith only [h2001, h2058, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2086 | h2086
                  · rcases h1bigk with h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h0, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1255, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1521, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1685, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1255, hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1521, hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1685, hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1995, hlam, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1521, h1995, hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1685, h1995, hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1996, hlam, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1998, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1685, h1995, h1998, hc01, hc12, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hc01, hc15, hlam, hphi, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1997, hlam, p2087_1]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h1999, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [h2000, hlam, p2087_0]
                    · have p2087_0 := h2087c.1
                      have p2087_1 := h2087c.2.1
                      have p2087_2 := h2087c.2.2.1
                      have p2087_3 := h2087c.2.2.2
                      linarith only [hlam, p2087_0]
                  · linarith only [h2000, h2001, h2086, hc23, hlam, hphi, ht34, ht45, u5elo1]
            · linarith only [h1521, h2000, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1255, h1999, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2116 | h2116
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2117 | h2117
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2118 | h2118
              · linarith only [h1685, h1998, h2116, h2118, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2120 | h2120
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2121 | h2121
                  · rcases h1bigk with h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h0, hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1255, hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1521, hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1685, hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1685, h2116, hc01, hc12, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1685, h1998, h2116, hc01, hc12, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1685, hc01, hc12, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1995, hlam, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1998, hlam, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1685, h1998, hc01, hc34, hlam, hphi, ht12, ht23, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1998, hc01, hc34, hlam, hphi, ht12, ht23, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1996, hlam, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1998, hc13, hc34, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1685, h1998, hc01, hc34, hlam, hphi, ht12, ht23, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h2116, hc01, hc13, hlam, hphi, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h1997, hlam, p2122_1]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h2116, hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [h2117, hlam, p2122_0]
                    · have p2122_0 := h2122c.1
                      have p2122_1 := h2122c.2.1
                      have p2122_2 := h2122c.2.2.1
                      have p2122_3 := h2122c.2.2.2
                      linarith only [hlam, p2122_0]
                  · linarith only [h1998, h2121, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h1998, h2116, h2120, hc23, hc34, hlam, hphi]
            · linarith only [h1998, h2116, h2117, hc35, hlam, hphi, u5elo4]
          · linarith only [h1255, h2116, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h1997, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2153 | h2153
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2154 | h2154
        · linarith only [h1995, h1996, h2154, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2156 | h2156
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2157 | h2157
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2158 | h2158
              · linarith only [h1685, h2154, h2156, h2158, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2160 | h2160
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2161 | h2161
                  · rcases h1bigk with h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c | h2162c
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h0, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1255, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1521, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1685, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1996, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1996, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1685, h1996, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1995, hlam, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h2154, hlam, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1685, h1995, h1996, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h0, h1996, h2158, hc02, hc34, hlam, hphi, ht23, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1996, h2158, hc13, hc34, hlam, hphi, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h1685, h1996, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h2156, hc01, hc13, hlam, hphi, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h2153, hlam, p2162_1]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h2156, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [h2157, hlam, p2162_0]
                    · have p2162_0 := h2162c.1
                      have p2162_1 := h2162c.2.1
                      have p2162_2 := h2162c.2.2.1
                      have p2162_3 := h2162c.2.2.2
                      linarith only [hlam, p2162_0]
                  · linarith only [h1996, h2158, h2161, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h1995, h1996, h2156, h2158, h2160, hc23, hc34, hlam, hphi]
            · linarith only [h1521, h2157, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1255, h2156, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h2153, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2193 | h2193
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2194 | h2194
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2195 | h2195
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2196 | h2196
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2197 | h2197
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2198 | h2198
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2199 | h2199
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2200 | h2200
                  · rcases h1bigk with h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c | h2201c
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h0, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1255, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1521, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1685, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1995, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1995, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1685, h1995, hc01, hc23, hlam, hphi, ht12, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1995, hc12, hc23, hlam, hphi, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1685, h1995, h2197, hc01, hc23, hlam, hphi, ht12, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1685, h1995, hc01, hc23, hlam, hphi, ht12, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h2193, hlam, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h2195, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h1685, h2193, hc01, hc12, hlam, hphi, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hc01, hc15, hlam, hphi, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h2194, hlam, p2201_1]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h2196, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [h2197, hlam, p2201_0]
                    · have p2201_0 := h2201c.1
                      have p2201_1 := h2201c.2.1
                      have p2201_2 := h2201c.2.2.1
                      have p2201_3 := h2201c.2.2.2
                      linarith only [hlam, p2201_0]
                  · rcases h1bigk with h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c | h2227c
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h0, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1255, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1521, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1685, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1995, hc01, hc23, hlam, hphi, ht12, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1995, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1995, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1995, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1995, hc01, hc23, hlam, hphi, ht12, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1995, hc12, hc23, hlam, hphi, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1521, h1995, hc01, hc23, hlam, hphi, ht12, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1685, h1995, hc01, hc23, hlam, hphi, ht12, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h2193, hc01, hc12, hlam, hphi, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h2193, hlam, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h2195, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h1685, h1995, h2193, hc01, hc23, hlam, hphi, ht12, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [hc01, hc15, hlam, hphi, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h2194, hlam, p2227_1]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h2196, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [h2197, hlam, p2227_0]
                    · have p2227_0 := h2227c.1
                      have p2227_1 := h2227c.2.1
                      have p2227_2 := h2227c.2.2.1
                      have p2227_3 := h2227c.2.2.2
                      linarith only [hlam, p2227_0]
                · linarith only [h1995, h2199, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1685, h1995, h2193, h2197, h2198, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h1521, h2197, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1255, h2196, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
        · linarith only [h1995, h2193, h2195, hlam]
      · linarith only [h0, h2194, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2259 | h2259
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2260 | h2260
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2261 | h2261
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2262 | h2262
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2263 | h2263
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2264 | h2264
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2265 | h2265
                  · rcases h1bigk with h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c | h2266c
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h0, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1255, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1521, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1685, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hc01, hc12, hlam, hphi, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1995, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2193, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2193, h2263, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hc01, hc13, hlam, hphi, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1995, hc12, hc23, hlam, hphi, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1521, h1995, hc01, hc23, hlam, hphi, ht12, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1685, h1995, hc01, hc23, hlam, hphi, ht12, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1685, h2193, h2259, h2263, hc01, hc23, hlam, hphi, ht12, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2260, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h1685, h2193, h2263, hc01, hc23, hlam, hphi, ht12, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2259, hc01, hc12, hlam, hphi, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2259, hlam, p2266_1]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2261, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [h2262, hlam, p2266_0]
                    · have p2266_0 := h2266c.1
                      have p2266_1 := h2266c.2.1
                      have p2266_2 := h2266c.2.2.1
                      have p2266_3 := h2266c.2.2.2
                      linarith only [hlam, p2266_0]
                  · rcases h1bigk with h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c | h2292c
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h0, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1255, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1521, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1685, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2193, h2263, hc01, hc23, hlam, hphi, ht12, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1995, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2193, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2193, h2263, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1995, hc01, hc23, hlam, hphi, ht12, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1995, hc12, hc23, hlam, hphi, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1521, h1995, hc01, hc23, hlam, hphi, ht12, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1685, h1995, hc01, hc23, hlam, hphi, ht12, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [hc01, hc14, hlam, hphi, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1685, h2193, h2259, h2263, hc01, hc23, hlam, hphi, ht12, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2260, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h1685, h2193, h2263, hc01, hc23, hlam, hphi, ht12, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2259, hc01, hc12, hlam, hphi, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2259, hlam, p2292_1]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2261, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [h2262, hlam, p2292_0]
                    · have p2292_0 := h2292c.1
                      have p2292_1 := h2292c.2.1
                      have p2292_2 := h2292c.2.2.1
                      have p2292_3 := h2292c.2.2.2
                      linarith only [hlam, p2292_0]
                · linarith only [h2193, h2263, h2264, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1685, h1995, h2259, h2263, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h1521, h2262, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h2260, h2261, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2322 | h2322
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2323 | h2323
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2324 | h2324
              · linarith only [h1685, h1995, h2259, h2260, h2324, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h1685, h1995, h2259, h2324, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h1685, h1995, h2259, h2260, h2323, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h1685, h1995, h2259, h2322, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h2259, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1255 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1685 | h1685
  · exact r1l7_21_15_H_I_L_0_x1_x1_x1_x0 m hb1 hb5 h0 h1255 h1521 h1685
  · exact r1l7_21_15_H_I_L_0_x1_x1_x1_x1 m hb1 hb5 h0 h1255 h1521 h1685

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1255 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1521 | h1521
  · exact r1l7_21_15_H_I_L_0_x1_x1_x0 m hb1 hb5 h0 h1255 h1521
  · exact r1l7_21_15_H_I_L_0_x1_x1_x1 m hb1 hb5 h0 h1255 h1521

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1255 | h1255
  · exact r1l7_21_15_H_I_L_0_x1_x0 m hb1 hb5 h0 h1255
  · exact r1l7_21_15_H_I_L_0_x1_x1 m hb1 hb5 h0 h1255

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_H_I_L_0_x0 m hb1 hb5 h0
  · exact r1l7_21_15_H_I_L_0_x1 m hb1 hb5 h0

end R2N4
