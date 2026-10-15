import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1482 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1725 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1764 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h1765 | h1765
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1766 | h1766
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1767 | h1767
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1768 | h1768
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1769 | h1769
          · rcases h1bigk with h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h0, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1178, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1482, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1725, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1767, h1769, hc12, hlam, hphi, ht01, ht0b, ht5b, p1770_1, u5ehi1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1769, hc12, hlam, hphi, ht01, ht0b, ht5b, p1770_1, u5ehi4]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1725, hc01, hc12, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1764, hlam, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1764, h1769, hc12, hlam, hphi, ht01, ht0b, ht5b, p1770_1, u5ehi4]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1725, h1764, hc01, hc12, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1765, hlam, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1767, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1725, h1764, h1767, hc01, hc12, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1766, hlam, p1770_1]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1768, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [h1769, hlam, p1770_0]
            · have p1770_0 := h1770c.1
              have p1770_1 := h1770c.2.1
              have p1770_2 := h1770c.2.2.1
              have p1770_3 := h1770c.2.2.2
              linarith only [hlam, p1770_0]
          · rcases h1bigk with h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h0, hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1178, hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1482, hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1725, hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1178, hc01, hc12, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1482, hc01, hc12, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1796_1, u5ehi1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1764, hlam, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1482, h1764, hc01, hc12, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1725, h1764, hc01, hc12, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1765, hlam, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1767, hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1769, hlam, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1766, hlam, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1768, hlam, p1796_0]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [h1769, hc14, hc45, hlam, hphi, p1796_1]
            · have p1796_0 := h1796c.1
              have p1796_1 := h1796c.2.1
              have p1796_2 := h1796c.2.2.1
              have p1796_3 := h1796c.2.2.2
              linarith only [hlam, p1796_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1822 | h1822
          · linarith only [h1767, h1768, h1822, hlam]
          · rcases h1bigk with h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h0, hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1178, hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1482, hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1725, hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1482, h1767, hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1482, hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1482, h1767, h1768, hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1764, hlam, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1482, h1766, h1768, hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1768, hlam, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1765, hlam, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1767, hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hlam, p1824_0]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1822, hlam, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1766, hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1766, hlam, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1178, h1766, hc01, hc12, hlam, hphi, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [h1482, h1822, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1824_1]
            · have p1824_0 := h1824c.1
              have p1824_1 := h1824c.2.1
              have p1824_2 := h1824c.2.2.1
              have p1824_3 := h1824c.2.2.2
              linarith only [hlam, p1824_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1850 | h1850
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1851 | h1851
          · rcases h1bigk with h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h0, hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1178, hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1482, hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1725, hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1850, hc12, hlam, hphi, ht01, ht0b, ht5b, p1852_1, u5ehi3]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1767, h1850, hc12, hlam, hphi, ht01, ht0b, ht5b, p1852_1, u5ehi3]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1852_1, u5ehi1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1764, hlam, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1767, hlam, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1725, h1767, hc01, hc34, hlam, hphi, ht12, ht23, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1767, hc01, hc34, hlam, hphi, ht12, ht23, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1765, hlam, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1767, hc13, hc34, hlam, hphi, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1725, h1767, hc01, hc34, hlam, hphi, ht12, ht23, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1766, hlam, p1852_1]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1850, hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [h1851, hlam, p1852_0]
            · have p1852_0 := h1852c.1
              have p1852_1 := h1852c.2.1
              have p1852_2 := h1852c.2.2.1
              have p1852_3 := h1852c.2.2.2
              linarith only [hlam, p1852_0]
          · linarith only [h1767, h1850, h1851, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1879 | h1879
          · rcases h1bigk with h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c | h1880c
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h0, hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1178, hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1482, hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1725, hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1178, hc01, hc12, hlam, hphi, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1879, hc12, hlam, hphi, ht01, ht0b, ht5b, p1880_1, u5ehi4]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1880_1, u5ehi1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1764, hlam, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1767, hlam, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1850, hlam, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1765, hlam, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1767, hc13, hc34, hlam, hphi, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1178, h1767, h1850, hc01, hc34, hlam, hphi, ht12, ht23, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1766, hlam, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1178, h1850, hc01, hc35, hlam, hphi, ht12, ht23, p1880_1]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [h1879, hlam, p1880_0]
            · have p1880_0 := h1880c.1
              have p1880_1 := h1880c.2.1
              have p1880_2 := h1880c.2.2.1
              have p1880_3 := h1880c.2.2.2
              linarith only [hlam, p1880_0]
          · rcases h1bigk with h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c | h1906c
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h0, hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1178, hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1482, hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1725, hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1178, hc01, hc12, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1482, hc01, hc12, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1906_1, u5ehi1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1764, hlam, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1767, hlam, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1850, hlam, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1765, hlam, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1767, hc13, hc34, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hlam, p1906_0]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1879, hlam, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1766, hlam, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1178, h1850, hc01, hc35, hlam, hphi, ht12, ht23, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [h1879, hc14, hc45, hlam, hphi, p1906_1]
            · have p1906_0 := h1906c.1
              have p1906_1 := h1906c.2.1
              have p1906_2 := h1906c.2.2.1
              have p1906_3 := h1906c.2.2.2
              linarith only [hlam, p1906_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1932 | h1932
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1933 | h1933
        · linarith only [h1764, h1766, h1933, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1935 | h1935
          · linarith only [h1764, h1766, h1932, h1935, hlam]
          · rcases h1bigk with h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c | h1937c
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h0, hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1178, hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1482, hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1725, hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1766, h1932, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1482, h1766, hc01, hc15, hlam, hphi, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1766, hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1764, hlam, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1482, h1933, hc01, hc35, hlam, hphi, ht12, ht23, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1933, hlam, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1765, hlam, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1932, hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hlam, p1937_0]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1935, hlam, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1766, hc01, hc25, hlam, hphi, ht12, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h0, h1766, hc02, hc25, hlam, hphi, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1933, hc13, hc35, hlam, hphi, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [h1482, h1935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1937_1]
            · have p1937_0 := h1937c.1
              have p1937_1 := h1937c.2.1
              have p1937_2 := h1937c.2.2.1
              have p1937_3 := h1937c.2.2.2
              linarith only [hlam, p1937_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1963 | h1963
        · linarith only [h1764, h1766, h1963, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1965 | h1965
          · linarith only [h1765, h1766, h1965, hlam]
          · rcases h1bigk with h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h0, hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1178, hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1482, hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1725, hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1178, h1766, hc01, hc15, hlam, hphi, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1178, h1766, h1932, hc01, hc15, hlam, hphi, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1766, hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1764, hlam, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1932, hlam, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1963, hlam, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1965, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1765, hlam, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1965, hc13, hc45, hlam, hphi, ht34, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hlam, p1967_0]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1965, hlam, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1766, hc01, hc25, hlam, hphi, ht12, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1766, hc12, hc25, hlam, hphi, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1178, h1963, hc01, hc35, hlam, hphi, ht12, ht23, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [h1178, h1932, h1965, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1967_1]
            · have p1967_0 := h1967c.1
              have p1967_1 := h1967c.2.1
              have p1967_2 := h1967c.2.2.1
              have p1967_3 := h1967c.2.2.2
              linarith only [hlam, p1967_0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1993 | h1993
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1994 | h1994
      · linarith only [h1764, h1765, h1994, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1996 | h1996
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1997 | h1997
          · rcases h1bigk with h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h0, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1178, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1482, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1725, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1765, h1996, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1998_1, u5ehi3]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1765, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1765, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1998_1, u5ehi1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1764, hlam, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1994, hlam, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1725, h1994, hc01, hc34, hlam, hphi, ht12, ht23, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1994, hc01, hc34, hlam, hphi, ht12, ht23, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1994, hc12, hc34, hlam, hphi, ht23, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1178, h1994, hc01, hc34, hlam, hphi, ht12, ht23, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1725, h1994, hc01, hc34, hlam, hphi, ht12, ht23, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1993, hlam, p1998_1]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1996, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [h1997, hlam, p1998_0]
            · have p1998_0 := h1998c.1
              have p1998_1 := h1998c.2.1
              have p1998_2 := h1998c.2.2.1
              have p1998_3 := h1998c.2.2.2
              linarith only [hlam, p1998_0]
          · linarith only [h1764, h1765, h1996, h1997, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2025 | h2025
          · rcases h1bigk with h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c | h2026c
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h0, hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1178, hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1482, hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1725, hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1178, h1765, hc01, hc14, hlam, hphi, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1765, hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1765, hc14, hlam, hphi, ht01, ht0b, ht5b, p2026_1, u5ehi1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1764, hlam, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1994, hlam, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1996, hlam, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1993, hc14, hlam, hphi, ht01, ht0b, ht5b, p2026_1, u5ehi2]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1994, hc13, hc34, hlam, hphi, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1178, h1994, h1996, hc01, hc34, hlam, hphi, ht12, ht23, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1993, hlam, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h1178, h1765, h1993, hc01, hc24, hlam, hphi, ht12, p2026_1]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [h2025, hlam, p2026_0]
            · have p2026_0 := h2026c.1
              have p2026_1 := h2026c.2.1
              have p2026_2 := h2026c.2.2.1
              have p2026_3 := h2026c.2.2.2
              linarith only [hlam, p2026_0]
          · linarith only [h1765, h1993, h2025, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2053 | h2053
      · linarith only [h1764, h1765, h2053, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2055 | h2055
        · linarith only [h1764, h1993, h2055, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2057 | h2057
          · rcases h1bigk with h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h0, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1178, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1482, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1725, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1993, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1765, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1993, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1764, hlam, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h2053, hlam, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h2055, hlam, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1765, hc12, hc24, hlam, hphi, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h2053, hc13, hc34, hlam, hphi, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h2053, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2058_1, u5ehi1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1178, h1764, h1993, hc01, hc25, hlam, hphi, ht12, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h1178, h2055, hc01, hc35, hlam, hphi, ht12, ht23, p2058_1]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [h2057, hlam, p2058_0]
            · have p2058_0 := h2058c.1
              have p2058_1 := h2058c.2.1
              have p2058_2 := h2058c.2.2.1
              have p2058_3 := h2058c.2.2.2
              linarith only [hlam, p2058_0]
          · rcases h1bigk with h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c | h2084c
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h0, hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1178, hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1482, hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1725, hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1178, hc01, hc12, hlam, hphi, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1765, hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1993, hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1764, hlam, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2053, hlam, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2055, hlam, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2057, hc12, hc45, hlam, hphi, ht23, ht34, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1178, h2057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hlam, p2084_0]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2057, hlam, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1178, h1764, h2057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h1178, h2057, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [h2057, hc14, hc45, hlam, hphi, p2084_1]
            · have p2084_0 := h2084c.1
              have p2084_1 := h2084c.2.1
              have p2084_2 := h2084c.2.2.1
              have p2084_3 := h2084c.2.2.2
              linarith only [hlam, p2084_0]

end R2N4
