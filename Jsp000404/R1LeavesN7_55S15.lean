import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S13
import Jsp000404.R1LeavesN7_55S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1352 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1405 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1478 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h1824 | h1824
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1825 | h1825
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1826 | h1826
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1827 | h1827
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1828 | h1828
          · rcases h1bigk with h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h0, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1108, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1352, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1405, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1478, hlam, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1478, h1828, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1829_1, u4ehi4]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1478, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1478, hc01, hc23, hlam, hphi, ht12, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1478, h1828, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1829_1, u4ehi4]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1405, h1478, hc01, hc23, hlam, hphi, ht12, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1824, hc01, hc12, hlam, hphi, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1824, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1826, hlam, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1405, h1478, h1824, hc01, hc23, hlam, hphi, ht12, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1829_1]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1825, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1827, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [h1828, hlam, p1829_0]
            · have p1829_0 := h1829c.1
              have p1829_1 := h1829c.2.1
              have p1829_2 := h1829c.2.2.1
              have p1829_3 := h1829c.2.2.2
              linarith only [hlam, p1829_0]
          · rcases h1bigk with h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h0, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1108, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1352, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1405, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, hc01, hc23, hlam, hphi, ht12, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, hlam, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1855_1, u4ehi1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, hc01, hc23, hlam, hphi, ht12, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1352, h1478, hc01, hc23, hlam, hphi, ht12, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1405, h1478, hc01, hc23, hlam, hphi, ht12, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1824, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1826, hlam, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1828, hlam, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1855_1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1825, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1827, hlam, p1855_0]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [h1478, h1825, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1855_1, u4ehi1]
            · have p1855_0 := h1855c.1
              have p1855_1 := h1855c.2.1
              have p1855_2 := h1855c.2.2.1
              have p1855_3 := h1855c.2.2.2
              linarith only [hlam, p1855_0]
        · linarith only [h1478, h1825, h1827, hlam]
      · linarith only [h1478, h1824, h1826, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1883 | h1883
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1884 | h1884
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1885 | h1885
          · linarith only [h1824, h1825, h1885, hlam]
          · rcases h1bigk with h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c | h1887c
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h0, hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1108, hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1352, hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1405, hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1478, hlam, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1825, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1887_1, u4ehi1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1825, hlam, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1478, hc01, hc23, hlam, hphi, ht12, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1352, h1478, hc01, hc23, hlam, hphi, ht12, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1405, h1478, hc01, hc23, hlam, hphi, ht12, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1824, hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1883, hlam, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1885, hlam, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1825, hc12, hc25, hlam, hphi, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1884, hlam, p1887_0]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [h1352, h1885, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1887_1]
            · have p1887_0 := h1887c.1
              have p1887_1 := h1887c.2.1
              have p1887_2 := h1887c.2.2.1
              have p1887_3 := h1887c.2.2.2
              linarith only [hlam, p1887_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1913 | h1913
          · linarith only [h1824, h1825, h1913, hlam]
          · rcases h1bigk with h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h0, hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1108, hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1352, hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1405, hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1478, h1884, hc01, hc35, hlam, hphi, ht12, ht23, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1478, hlam, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1478, h1884, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1915_1, u4ehi1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1825, hlam, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1884, hc01, hc35, hlam, hphi, ht12, ht23, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1884, hc12, hc35, hlam, hphi, ht23, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1352, h1884, hc01, hc35, hlam, hphi, ht12, ht23, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1884, hlam, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1824, hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1883, hlam, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hlam, p1915_0]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1913, hlam, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1824, h1825, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1915_1, u4ehi2]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1884, hc13, hc35, hlam, hphi, p1915_1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [h1913, hc45, hlam, hphi, p1915_1, u4ehi1]
            · have p1915_0 := h1915c.1
              have p1915_1 := h1915c.2.1
              have p1915_2 := h1915c.2.2.1
              have p1915_3 := h1915c.2.2.2
              linarith only [hlam, p1915_0]
      · linarith only [h1478, h1824, h1883, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1942 | h1942
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1943 | h1943
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1944 | h1944
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1945 | h1945
          · rcases h1bigk with h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h0, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1108, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1352, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1405, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1478, hlam, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1824, hlam, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1824, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1478, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1946_1, u4ehi1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1405, h1478, hc01, hc23, hlam, hphi, ht12, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1405, h1824, h1942, hc01, hc24, hlam, hphi, ht12, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1943, hlam, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1405, h1478, h1943, hc01, hc23, hlam, hphi, ht12, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1942, hc01, hc12, hlam, hphi, p1946_1]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1942, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1944, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [h1945, hlam, p1946_0]
            · have p1946_0 := h1946c.1
              have p1946_1 := h1946c.2.1
              have p1946_2 := h1946c.2.2.1
              have p1946_3 := h1946c.2.2.2
              linarith only [hlam, p1946_0]
          · linarith only [h1824, h1942, h1945, hlam]
        · linarith only [h1478, h1942, h1944, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1974 | h1974
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1975 | h1975
          · rcases h1bigk with h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h0, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1108, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1352, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1405, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1478, hlam, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1824, hlam, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1478, h1943, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1943, hc01, hc34, hlam, hphi, ht12, ht23, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1943, hc12, hc34, hlam, hphi, ht23, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1943, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1405, h1943, hc01, hc34, hlam, hphi, ht12, ht23, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1943, hc01, hc34, hlam, hphi, ht12, ht23, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1405, h1942, h1943, hc01, hc34, hlam, hphi, ht12, ht23, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1943, hc13, hc34, hlam, hphi, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1405, h1943, hc01, hc34, hlam, hphi, ht12, ht23, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1942, hc01, hc12, hlam, hphi, p1976_1]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1942, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1974, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [h1975, hlam, p1976_0]
            · have p1976_0 := h1976c.1
              have p1976_1 := h1976c.2.1
              have p1976_2 := h1976c.2.2.1
              have p1976_3 := h1976c.2.2.2
              linarith only [hlam, p1976_0]
          · linarith only [h1478, h1942, h1943, h1975, hlam]
        · linarith only [h1478, h1942, h1974, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2004 | h2004
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2005 | h2005
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2006 | h2006
          · rcases h1bigk with h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c | h2007c
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h0, hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1108, hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1352, hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1405, hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1478, hlam, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1824, hlam, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1942, hlam, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1478, h2006, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2007_1, u4ehi4]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h1405, h1478, hc01, hc23, hlam, hphi, ht12, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h0, h1824, hc01, hc24, hlam, hphi, ht12, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h2004, hlam, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h0, h1478, h1942, h2004, hc01, hc23, hlam, hphi, ht12, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h0, h1942, hc01, hc25, hlam, hphi, ht12, p2007_1]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h2005, hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [h2006, hlam, p2007_0]
            · have p2007_0 := h2007c.1
              have p2007_1 := h2007c.2.1
              have p2007_2 := h2007c.2.2.1
              have p2007_3 := h2007c.2.2.2
              linarith only [hlam, p2007_0]
          · rcases h1bigk with h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h0, hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1108, hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1352, hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1405, hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1478, hlam, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1824, hlam, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1942, hlam, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1478, hc01, hc23, hlam, hphi, ht12, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1478, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2033_1, u4ehi1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h1405, h1478, hc01, hc23, hlam, hphi, ht12, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h0, h1824, hc01, hc24, hlam, hphi, ht12, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h2004, hlam, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h2006, hlam, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h0, h1942, hc01, hc25, hlam, hphi, ht12, p2033_1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h2005, hlam, p2033_0]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [h2006, hc45, hlam, hphi, p2033_1, u4ehi1]
            · have p2033_0 := h2033c.1
              have p2033_1 := h2033c.2.1
              have p2033_2 := h2033c.2.2.1
              have p2033_3 := h2033c.2.2.2
              linarith only [hlam, p2033_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2059 | h2059
          · linarith only [h2004, h2005, h2059, hlam]
          · rcases h1bigk with h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h0, hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1108, hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1352, hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1405, hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1478, hlam, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1824, hlam, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1942, hlam, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1478, hc12, hc23, hlam, hphi, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1478, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2061_1, u4ehi1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h2005, hlam, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h0, h1824, hc01, hc24, hlam, hphi, ht12, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h2004, hlam, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hlam, p2061_0]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h2059, hlam, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h1942, hc01, hc25, hlam, hphi, ht12, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h0, h1942, hc01, hc25, hlam, hphi, ht12, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h2005, hc13, hc35, hlam, hphi, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [h0, h1824, h2059, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2061_1]
            · have p2061_0 := h2061c.1
              have p2061_1 := h2061c.2.1
              have p2061_2 := h2061c.2.2.1
              have p2061_3 := h2061c.2.2.2
              linarith only [hlam, p2061_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2087 | h2087
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2088 | h2088
          · rcases h1bigk with h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h0, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h1108, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h1352, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h1405, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h1478, hlam, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h1824, hlam, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h1942, hlam, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2004, hc01, hc34, hlam, hphi, ht12, ht23, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2004, hc12, hc34, hlam, hphi, ht23, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2004, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2004, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h0, h1824, hc01, hc24, hlam, hphi, ht12, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2004, hc13, hc34, hlam, hphi, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h0, h1942, h2004, hc01, hc34, hlam, hphi, ht12, ht23, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2087, hc01, hc13, hlam, hphi, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h0, h1478, h2087, hc01, hc23, hlam, hphi, ht12, p2089_1]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2087, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [h2088, hlam, p2089_0]
            · have p2089_0 := h2089c.1
              have p2089_1 := h2089c.2.1
              have p2089_2 := h2089c.2.2.1
              have p2089_3 := h2089c.2.2.2
              linarith only [hlam, p2089_0]
          · linarith only [h2004, h2087, h2088, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2116 | h2116
          · rcases h1bigk with h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c | h2117c
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h0, hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1108, hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1352, hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1405, hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1478, hlam, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1824, hlam, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1942, hlam, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h2087, hc12, hc35, hlam, hphi, ht23, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h2004, hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h2087, hlam, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hc01, hc14, hlam, hphi, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h0, h1824, hc01, hc24, hlam, hphi, ht12, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h2004, hc13, hc34, hlam, hphi, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h1405, h2004, hc01, hc34, hlam, hphi, ht12, ht23, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hc01, hc15, hlam, hphi, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h0, h1942, hc01, hc25, hlam, hphi, ht12, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h0, h1478, h2087, hc01, hc35, hlam, hphi, ht12, ht23, p2117_1]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [h2116, hlam, p2117_0]
            · have p2117_0 := h2117c.1
              have p2117_1 := h2117c.2.1
              have p2117_2 := h2117c.2.2.1
              have p2117_3 := h2117c.2.2.2
              linarith only [hlam, p2117_0]
          · rcases h1bigk with h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h0, hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h1108, hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h1352, hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h1405, hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hc01, hc12, hlam, hphi, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h1478, hlam, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h1824, hlam, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h1942, hlam, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hc01, hc13, hlam, hphi, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h0, hc01, hc13, hlam, hphi, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2004, hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2087, hlam, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2116, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h0, h2116, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2116, hc13, hc45, hlam, hphi, ht34, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hlam, p2143_0]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2116, hlam, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2116, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h0, h2116, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h0, h1478, h2116, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2143_1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [h2116, hc45, hlam, hphi, p2143_1, u4ehi1]
            · have p2143_0 := h2143c.1
              have p2143_1 := h2143c.2.1
              have p2143_2 := h2143c.2.2.1
              have p2143_3 := h2143c.2.2.2
              linarith only [hlam, p2143_0]

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1352 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1405 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1478 | h1478
  · exact r1l7_21_14_H_I_L_R_x1_x1_x1_x1_x0 m hb1 hb4 h0 h1108 h1352 h1405 h1478
  · exact r1l7_21_14_H_I_L_R_x1_x1_x1_x1_x1 m hb1 hb4 h0 h1108 h1352 h1405 h1478

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1352 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1405 | h1405
  · exact r1l7_21_14_H_I_L_R_x1_x1_x1_x0 m hb1 hb4 h0 h1108 h1352 h1405
  · exact r1l7_21_14_H_I_L_R_x1_x1_x1_x1 m hb1 hb4 h0 h1108 h1352 h1405

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1352 | h1352
  · exact r1l7_21_14_H_I_L_R_x1_x1_x0 m hb1 hb4 h0 h1108 h1352
  · exact r1l7_21_14_H_I_L_R_x1_x1_x1 m hb1 hb4 h0 h1108 h1352

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1108 | h1108
  · exact r1l7_21_14_H_I_L_R_x1_x0 m hb1 hb4 h0 h1108
  · exact r1l7_21_14_H_I_L_R_x1_x1 m hb1 hb4 h0 h1108

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_H_I_L_R_x0 m hb1 hb4 h0
  · exact r1l7_21_14_H_I_L_R_x1 m hb1 hb4 h0

end R2N4
