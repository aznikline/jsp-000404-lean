import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1741 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1742 | h1742
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1743 | h1743
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1746 | h1746
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1747 | h1747
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1748 | h1748
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1749 | h1749
                · rcases h5bigk with h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [hlam, p1750_0]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h0, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h0, h1743, h1747, h1749, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h0, h1743, h1749, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h0, h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [hlam, p1750_0]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, h1747, h1749, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, h1749, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1741, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [hlam, p1750_0]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1741, h1749, hc02, hc45, hlam, hphi, ht0b, ht5b, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1744, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1747, hlam, p1750_0]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [hlam, p1750_0]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1743, h1747, hc45, hlam, hphi, ht01, ht0b, ht5b, p1750_1, u1elo1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1742, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1745, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1748, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [h1749, hlam, p1750_1]
                  · have p1750_0 := h1750c.1
                    have p1750_1 := h1750c.2.1
                    have p1750_2 := h1750c.2.2.1
                    have p1750_3 := h1750c.2.2.2
                    linarith only [hlam, p1750_0]
                · rcases h5bigk with h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [hlam, p1776_0]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h0, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h0, h1743, hc25, hlam, hphi, ht01, ht0b, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h0, h1743, hc35, hlam, hphi, ht01, ht0b, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h0, h1743, h1749, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [hlam, p1776_0]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1743, h1748, h1749, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1743, hc35, hlam, hphi, ht01, ht0b, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1743, h1749, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1741, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1743, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [hlam, p1776_0]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h0, h1741, h1743, hc35, hlam, hphi, ht01, ht0b, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1743, h1749, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1776_1, u1elo1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1744, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1747, hlam, p1776_0]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [hlam, p1776_0]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1749, hlam, p1776_0]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1742, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1745, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1748, hlam, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [h1748, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1776_1]
                  · have p1776_0 := h1776c.1
                    have p1776_1 := h1776c.2.1
                    have p1776_2 := h1776c.2.2.1
                    have p1776_3 := h1776c.2.2.2
                    linarith only [hlam, p1776_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1802 | h1802
                · linarith only [h1746, h1748, h1802, hlam]
                · rcases h5bigk with h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h0, hlam, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h0, h1743, hc25, hlam, hphi, ht01, ht0b, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h0, h1743, h1802, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h0, h1743, h1748, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1743, h1748, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1743, h1802, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1743, h1748, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1804_1, u1elo1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1741, hlam, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1743, hlam, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1741, h1802, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1748, hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1744, hlam, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1747, hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1802, hlam, p1804_0]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1742, hlam, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1745, hlam, p1804_1]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1745, hc25, hlam, hphi, ht01, ht0b, ht5b, p1804_1, u1elo3]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [h1745, hc35, hlam, hphi, ht01, ht0b, ht5b, p1804_1, u1elo3]
                  · have p1804_0 := h1804c.1
                    have p1804_1 := h1804c.2.1
                    have p1804_2 := h1804c.2.2.1
                    have p1804_3 := h1804c.2.2.2
                    linarith only [hlam, p1804_0]
            · linarith only [h1744, h1746, h1747, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1831 | h1831
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1832 | h1832
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1833 | h1833
                · rcases h5bigk with h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c | h1834c
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [hlam, p1834_0]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h0, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h0, h1743, hc25, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h0, h1743, hc35, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h0, h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [hlam, p1834_0]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1743, hc25, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1743, h1833, hc45, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1741, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1743, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [hlam, p1834_0]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1741, h1833, hc02, hc45, hlam, hphi, ht0b, ht5b, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1834_1, u1elo1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1744, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1831, hlam, p1834_0]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [hlam, p1834_0]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1746, h1831, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1742, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1745, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1832, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [h1833, hlam, p1834_1]
                  · have p1834_0 := h1834c.1
                    have p1834_1 := h1834c.2.1
                    have p1834_2 := h1834c.2.2.1
                    have p1834_3 := h1834c.2.2.2
                    linarith only [hlam, p1834_0]
                · linarith only [h1742, h1746, h1831, h1833, hc04, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h1745, h1746, h1831, h1832, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1862 | h1862
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1863 | h1863
                · rcases h5bigk with h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [hlam, p1864_0]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h0, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h0, h1743, hc25, hlam, hphi, ht01, ht0b, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h0, h1743, h1831, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h0, h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [hlam, p1864_0]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1743, h1831, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1743, h1831, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1864_1, u1elo1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1741, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1743, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [hlam, p1864_0]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1831, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1741, hc02, hc45, hlam, hphi, ht0b, ht5b, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h0, h1863, hc01, hc34, hlam, hphi, ht12, ht23, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1744, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1744, hc25, hlam, hphi, ht01, ht0b, ht5b, p1864_1, u1elo2]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [hlam, p1864_0]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1744, hc45, hlam, hphi, ht01, ht0b, ht5b, p1864_1, u1elo2]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1742, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1745, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1862, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [h1863, hlam, p1864_1]
                  · have p1864_0 := h1864c.1
                    have p1864_1 := h1864c.2.1
                    have p1864_2 := h1864c.2.2.1
                    have p1864_3 := h1864c.2.2.2
                    linarith only [hlam, p1864_0]
                · linarith only [h1745, h1746, h1863, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1891 | h1891
                · rcases h5bigk with h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [hlam, p1892_0]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h0, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h0, h1743, h1746, h1862, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h0, h1743, hc35, hlam, hphi, ht01, ht0b, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h0, h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [hlam, p1892_0]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1743, h1746, h1862, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1743, h1891, hc45, hlam, hphi, ht01, ht0b, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1892_1, u1elo1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1741, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1743, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [hlam, p1892_0]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1831, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1862, hlam, p1892_0]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1742, h1746, h1862, hc23, hc35, hlam, hphi, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1744, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1744, h1746, h1862, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1892_1, u1elo2]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [hlam, p1892_0]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1744, h1746, h1862, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1892_1, u1elo2]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1742, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1745, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1746, h1862, h1891, hc23, hc34, hlam, hphi, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [h1891, hlam, p1892_1]
                  · have p1892_0 := h1892c.1
                    have p1892_1 := h1892c.2.1
                    have p1892_2 := h1892c.2.2.1
                    have p1892_3 := h1892c.2.2.2
                    linarith only [hlam, p1892_0]
                · linarith only [h1745, h1746, h1891, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · linarith only [h0, h1742, h1745, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1920 | h1920
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1921 | h1921
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1922 | h1922
            · linarith only [h0, h1741, h1744, h1922, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1924 | h1924
              · linarith only [h1921, h1922, h1924, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1926 | h1926
                · linarith only [h1921, h1922, h1924, h1926, hlam]
                · linarith only [h0, h1744, h1920, h1926, hc01, hlam, hphi, u1elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1929 | h1929
            · linarith only [h0, h1744, h1921, h1929, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1931 | h1931
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1932 | h1932
                · rcases h5bigk with h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c | h1933c
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [hlam, p1933_0]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h0, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p1933_1, u1elo4]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h0, h1744, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h0, h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1933_1, u1elo1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1933_1, u1elo1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [hlam, p1933_0]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1743, h1929, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1933_1, u1elo1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1744, hlam, p1933_0]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1933_1, u1elo1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1741, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1743, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [hlam, p1933_0]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1929, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1741, hc02, hc45, hlam, hphi, ht0b, ht5b, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1929, hc23, hc35, hlam, hphi, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [hlam, p1933_0]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    rcases p1933_3 (m.d 0 5) (by simp) with h1953 | h1953
                    · linarith only [h0, h1744, h1953, hlam]
                    · linarith only [h1742, h1953, hlam]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1742, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1920, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1931, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [h1932, hlam, p1933_1]
                  · have p1933_0 := h1933c.1
                    have p1933_1 := h1933c.2.1
                    have p1933_2 := h1933c.2.2.1
                    have p1933_3 := h1933c.2.2.2
                    linarith only [hlam, p1933_0]
                · linarith only [h1920, h1921, h1932, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1962 | h1962
                · rcases h5bigk with h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [hlam, p1963_0]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h0, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h0, h1743, h1921, h1931, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1963_1, u1elo1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h0, h1744, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h0, h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1963_1, u1elo1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1743, hc05, hlam, hphi, ht01, ht0b, ht5b, p1963_1, u1elo1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [hlam, p1963_0]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1743, h1921, h1931, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1963_1, u1elo1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1744, hlam, p1963_0]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1743, hc45, hlam, hphi, ht01, ht0b, ht5b, p1963_1, u1elo1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1741, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1743, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [hlam, p1963_0]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1929, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1931, hlam, p1963_0]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1742, h1921, h1931, hc23, hc35, hlam, hphi, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1921, h1931, hc23, hc35, hlam, hphi, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [hlam, p1963_0]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1921, h1931, h1962, hc23, hc34, hlam, hphi, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1742, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1920, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h0, h1742, h1921, h1931, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1963_1, u1elo4]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [h1962, hlam, p1963_1]
                  · have p1963_0 := h1963c.1
                    have p1963_1 := h1963c.2.1
                    have p1963_2 := h1963c.2.2.1
                    have p1963_3 := h1963c.2.2.2
                    linarith only [hlam, p1963_0]
                · linarith only [h1920, h1921, h1962, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · linarith only [h0, h1742, h1920, hlam]
    · linarith only [h0, h1741, h1743, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1992 | h1992
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1993 | h1993
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1994 | h1994
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1995 | h1995
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1996 | h1996
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1997 | h1997
              · linarith only [h1741, h1742, h1997, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1999 | h1999
                · linarith only [h1995, h1997, h1999, hlam]
                · rcases h5bigk with h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c | h2001c
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h0, hlam, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h0, h1996, hc35, hlam, hphi, ht01, ht0b, ht5b, p2001_1, u1elo4]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1742, h1994, h1999, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2001_1, u1elo3]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1742, hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1992, hc05, hlam, hphi, ht01, ht0b, ht5b, p2001_1, u1elo1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1992, h1997, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2001_1, u1elo1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1992, h1999, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2001_1, u1elo1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1742, h1992, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2001_1, u1elo1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1741, hlam, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1992, hlam, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1741, h1999, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1997, hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1993, hlam, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1996, hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1999, hlam, p2001_0]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h0, h1994, hc01, hlam, hphi, p2001_1, u1elo3]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1994, hlam, p2001_1]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1994, hc25, hlam, hphi, ht01, ht0b, ht5b, p2001_1, u1elo3]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [h1994, hc35, hlam, hphi, ht01, ht0b, ht5b, p2001_1, u1elo3]
                  · have p2001_0 := h2001c.1
                    have p2001_1 := h2001c.2.1
                    have p2001_2 := h2001c.2.2.1
                    have p2001_3 := h2001c.2.2.2
                    linarith only [hlam, p2001_0]
            · linarith only [h1993, h1995, h1996, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2028 | h2028
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2029 | h2029
              · linarith only [h1741, h1742, h2029, hlam]
              · linarith only [h1994, h1995, h2028, h2029, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2032 | h2032
              · linarith only [h1741, h1742, h2032, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2034 | h2034
                · rcases h5bigk with h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c | h2035c
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [hlam, p2035_0]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h0, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1742, h1993, h2034, hc25, hlam, hphi, ht01, ht0b, ht5b, p2035_1, u1elo2]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1742, h2034, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1742, hlam, p2035_0]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1992, hc05, hlam, hphi, ht01, ht0b, ht5b, p2035_1, u1elo1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [hlam, p2035_0]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1992, h1995, h2032, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2035_1, u1elo1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1992, hc35, hlam, hphi, ht01, ht0b, ht5b, p2035_1, u1elo1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1742, h1992, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p2035_1, u1elo1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1741, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1992, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [hlam, p2035_0]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h2028, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h2032, hlam, p2035_0]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1993, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1993, hc25, hlam, hphi, ht01, ht0b, ht5b, p2035_1, u1elo2]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [hlam, p2035_0]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1993, hc45, hlam, hphi, ht01, ht0b, ht5b, p2035_1, u1elo2]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1994, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h1994, h1995, h2032, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2035_1, u1elo3]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [h2034, hlam, p2035_1]
                  · have p2035_0 := h2035c.1
                    have p2035_1 := h2035c.2.1
                    have p2035_2 := h2035c.2.2.1
                    have p2035_3 := h2035c.2.2.2
                    linarith only [hlam, p2035_0]
                · linarith only [h1994, h1995, h2034, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2062 | h2062
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2063 | h2063
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2064 | h2064
              · linarith only [h0, h1992, h1994, h2064, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2066 | h2066
                · linarith only [h0, h1994, h2062, h2066, hc01, hc23, hlam, hphi, ht12]
                · rcases h5bigk with h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c | h2068c
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h0, hlam, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h0, h1992, h2064, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u1elo1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h0, h1992, hc35, hlam, hphi, ht01, ht0b, ht5b, p2068_1, u1elo1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1742, hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1992, hc05, hlam, hphi, ht01, ht0b, ht5b, p2068_1, u1elo1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1992, h2062, h2064, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2068_1, u1elo1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1992, hc35, hlam, hphi, ht01, ht0b, ht5b, p2068_1, u1elo1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1994, hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1741, hlam, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1992, hlam, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1741, hc02, hc35, hlam, hphi, ht0b, ht5b, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h2064, hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h1993, hlam, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h2063, hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h2066, hlam, p2068_0]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h2062, h2064, hc34, hc45, hlam, hphi, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [h2066, hc34, hc45, hlam, hphi, p2068_1]
                  · have p2068_0 := h2068c.1
                    have p2068_1 := h2068c.2.1
                    have p2068_2 := h2068c.2.2.1
                    have p2068_3 := h2068c.2.2.2
                    linarith only [hlam, p2068_0]
            · linarith only [h1993, h2062, h2063, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2095 | h2095
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2096 | h2096
              · linarith only [h1741, h1742, h2096, hlam]
              · linarith only [h2062, h2095, h2096, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
              · linarith only [h1741, h1742, h2099, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2101 | h2101
                · linarith only [h0, h1993, h1994, h2101, hc01, hlam, hphi, u1elo2]
                · rcases h5bigk with h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h0, hlam, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p2103_1, u1elo4]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2103_1, u1elo4]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1742, hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2103_1, u1elo4]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1992, h2062, h2099, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2103_1, u1elo1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1992, hc35, hlam, hphi, ht01, ht0b, ht5b, p2103_1, u1elo1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1994, hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1741, hlam, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1992, hlam, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h2095, hlam, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h2099, hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1993, hlam, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h1993, h2099, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2103_1, u1elo2]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h2101, hlam, p2103_0]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h2062, h2099, hc23, hc45, hlam, hphi, ht34, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [h2095, hc23, hc45, hlam, hphi, ht34, p2103_1]
                  · have p2103_0 := h2103c.1
                    have p2103_1 := h2103c.2.1
                    have p2103_2 := h2103c.2.2.1
                    have p2103_3 := h2103c.2.2.2
                    linarith only [hlam, p2103_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2129 | h2129
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2130 | h2130
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2131 | h2131
            · linarith only [h0, h1741, h1993, h2131, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2133 | h2133
              · linarith only [h1741, h1742, h2130, h2131, h2133, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2135 | h2135
                · linarith only [h1741, h1742, h2130, h2131, h2135, hlam]
                · linarith only [h0, h1993, h2129, h2135, hc01, hlam, hphi, u1elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2138 | h2138
            · linarith only [h0, h1993, h2130, h2138, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2140 | h2140
              · linarith only [h1741, h1742, h2140, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2142 | h2142
                · rcases h5bigk with h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h0, hlam, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1742, h2129, hc25, hlam, hphi, ht01, ht0b, ht5b, p2143_1, u1elo3]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h0, h1742, h1993, h2129, hc01, hlam, hphi, p2143_1, u1elo3]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1742, hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2143_1, u1elo4]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1992, h2130, h2140, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2143_1, u1elo1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1993, hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1992, hc45, hlam, hphi, ht01, ht0b, ht5b, p2143_1, u1elo1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1741, hlam, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h1992, hlam, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2138, hlam, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2140, hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2130, h2140, hc23, hc35, hlam, hphi, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [hlam, p2143_0]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2130, h2140, h2142, hc23, hc34, hlam, hphi, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2129, hlam, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2129, h2130, h2140, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2143_1, u1elo3]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [h2142, hlam, p2143_1]
                  · have p2143_0 := h2143c.1
                    have p2143_1 := h2143c.2.1
                    have p2143_2 := h2143c.2.2.1
                    have p2143_3 := h2143c.2.2.2
                    linarith only [hlam, p2143_0]
                · linarith only [h2129, h2130, h2142, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2170 | h2170
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2171 | h2171
            · linarith only [h0, h1741, h1993, h2171, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2173 | h2173
              · linarith only [h0, h1741, h2129, h2170, h2171, h2173, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2175 | h2175
                · linarith only [h0, h1741, h2129, h2170, h2171, h2175, hlam]
                · rcases h5bigk with h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c | h2177c
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h0, hlam, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p2177_1, u1elo4]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h0, h1993, hlam, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1742, hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2177_1, u1elo4]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1992, h2171, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2177_1, u1elo1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1993, hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h2129, hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1741, hlam, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1992, hlam, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h2171, hlam, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h2173, hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1741, h2170, h2171, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h0, h2175, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h2170, h2171, h2175, hc34, hc45, hlam, hphi, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h2175, hlam, p2177_0]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1741, h2170, h2171, hc34, hc45, hlam, hphi, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h2170, h2171, hc34, hc45, hlam, hphi, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [h1993, hc13, hc45, hlam, hphi, ht34, p2177_1]
                  · have p2177_0 := h2177c.1
                    have p2177_1 := h2177c.2.1
                    have p2177_2 := h2177c.2.2.1
                    have p2177_3 := h2177c.2.2.2
                    linarith only [hlam, p2177_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2203 | h2203
            · linarith only [h0, h1993, h2170, h2203, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2205 | h2205
              · linarith only [h1741, h1742, h2205, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2207 | h2207
                · rcases h5bigk with h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p2208_1, u1elo4]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, h2129, h2207, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h1742, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2129, h2207, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2129, h2170, h2205, h2207, hc23, hc34, hlam, hphi, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h1993, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2129, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h1741, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h1992, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2203, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2205, hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2170, h2205, hc23, hc35, hlam, hphi, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h1742, h2207, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2170, h2205, hc23, hc45, hlam, hphi, ht34, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [h2207, hlam, p2208_1]
                  · have p2208_0 := h2208c.1
                    have p2208_1 := h2208c.2.1
                    have p2208_2 := h2208c.2.2.1
                    have p2208_3 := h2208c.2.2.2
                    linarith only [hlam, p2208_0]
                · rcases h5bigk with h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c | h2234c
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, hlam, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, h2170, h2205, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2234_1, u1elo4]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, h1992, hc35, hlam, hphi, ht01, ht0b, ht5b, p2234_1, u1elo1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1742, hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1992, hc05, hlam, hphi, ht01, ht0b, ht5b, p2234_1, u1elo1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1992, h2170, h2205, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2234_1, u1elo1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1993, hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h2129, hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1741, hlam, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1992, hlam, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h2203, hlam, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h2205, hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h2170, h2205, hc23, hc35, hlam, hphi, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h2207, hlam, p2234_0]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h2170, h2205, hc23, hc45, hlam, hphi, ht34, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [h1993, hc13, hc45, hlam, hphi, ht34, p2234_1]
                  · have p2234_0 := h2234c.1
                    have p2234_1 := h2234c.2.1
                    have p2234_2 := h2234c.2.2.1
                    have p2234_3 := h2234c.2.2.2
                    linarith only [hlam, p2234_0]
    · linarith only [h0, h1741, h1992, hlam]

end R2N4
