import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1082 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1343 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1657 | h1657
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1658 | h1658
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1659 | h1659
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1660 | h1660
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1661 | h1661
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1662 | h1662
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1663 | h1663
              · rcases h0bigk with h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, hlam, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1082, hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1343, hlam, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1343, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1657, hc02, hc15, hlam, hphi, ht0b, ht5b, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, h1660, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1664_1, u3ehi3]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, h1662, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1664_1, u4ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, h1659, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1664_1, u3ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1657, h1659, h1663, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1664_1, u3ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1658, hlam, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, h1658, h1662, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1664_1, u4ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, h1658, h1659, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1664_1, u3ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1657, h1659, h1663, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1664_1, u3ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1658, h1660, hlam, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1660, hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h0, h1658, h1659, h1660, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1664_1, u3ehi4]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1657, hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1659, hlam, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1661, hlam, p1664_0]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [h1662, hlam, p1664_1]
                · have p1664_0 := h1664c.1
                  have p1664_1 := h1664c.2.1
                  have p1664_2 := h1664c.2.2.1
                  have p1664_3 := h1664c.2.2.2
                  linarith only [hlam, p1664_0]
              · rcases h0bigk with h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c | h1690c
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, hlam, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1082, hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1343, hlam, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1661, h1663, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, h1343, h1657, h1661, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, h1661, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1657, h1661, h1663, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1658, hlam, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, h1343, h1657, h1658, h1661, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, h1658, h1661, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1657, h1661, h1663, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1658, h1660, hlam, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1660, hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h0, h1658, h1660, h1661, h1663, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1690_1, u3ehi2]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1657, hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1659, hlam, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1661, hlam, p1690_0]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [h1662, hlam, p1690_1]
                · have p1690_0 := h1690c.1
                  have p1690_1 := h1690c.2.1
                  have p1690_2 := h1690c.2.2.1
                  have p1690_3 := h1690c.2.2.2
                  linarith only [hlam, p1690_0]
            · linarith only [h1343, h1657, h1662, hlam]
          · linarith only [h1660, h1661, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1718 | h1718
          · linarith only [h1660, h1718, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1082, h1657, h1718, hlam]
      · linarith only [h1082, h1657, h1658, h1659, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1722 | h1722
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1723 | h1723
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1724 | h1724
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1725 | h1725
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1726 | h1726
              · rcases h0bigk with h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h0, hlam, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1082, hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1343, hlam, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, hc01, hc23, hlam, hphi, ht12, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, h1725, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1727_1, u4ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, h1722, h1726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1727_1, u3ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1657, h1722, h1726, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1727_1, u3ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, hc02, hc23, hlam, hphi, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, h1725, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1727_1, u4ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, h1722, h1726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1727_1, u3ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1657, h1722, h1726, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1727_1, u3ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, h1722, h1723, h1726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1727_1, u3ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1723, hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1658, h1722, h1723, h1726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1727_1, u3ehi4]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1657, hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1722, hlam, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1724, hlam, p1727_0]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [h1725, hlam, p1727_1]
                · have p1727_0 := h1727c.1
                  have p1727_1 := h1727c.2.1
                  have p1727_2 := h1727c.2.2.1
                  have p1727_3 := h1727c.2.2.2
                  linarith only [hlam, p1727_0]
              · linarith only [h1658, h1723, h1726, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1343, h1657, h1725, hlam]
          · linarith only [h1723, h1724, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1756 | h1756
          · linarith only [h1723, h1756, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1082, h1657, h1756, hlam]
      · linarith only [h0, h1657, h1722, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1760 | h1760
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1761 | h1761
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1762 | h1762
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1763 | h1763
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1764 | h1764
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1765 | h1765
              · rcases h0bigk with h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1082, hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1343, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1657, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1766_1, u3ehi0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1766_1, u4ehi0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, h1657, hc01, hc12, hlam, hphi, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1760, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, h1760, h1764, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1766_1, u4ehi4]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, h1657, h1760, hc01, hc12, hlam, hphi, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1760, h1762, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1762, hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h0, h1760, h1761, h1762, h1765, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1766_1, u3ehi4]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1761, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1763, hlam, p1766_0]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [h1764, hlam, p1766_1]
                · have p1766_0 := h1766c.1
                  have p1766_1 := h1766c.2.1
                  have p1766_2 := h1766c.2.2.1
                  have p1766_3 := h1766c.2.2.2
                  linarith only [hlam, p1766_0]
              · rcases h0bigk with h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1082, hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1343, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1657, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1792_1, u3ehi0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1792_1, u4ehi0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, h1657, hc01, hc12, hlam, hphi, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1760, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, h1760, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1792_1, u4ehi0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, h1657, h1760, hc01, hc12, hlam, hphi, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1760, h1762, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1762, hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h0, h1760, h1762, h1763, h1765, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1792_1, u3ehi2]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1761, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1763, hlam, p1792_0]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [h1764, hlam, p1792_1]
                · have p1792_0 := h1792c.1
                  have p1792_1 := h1792c.2.1
                  have p1792_2 := h1792c.2.2.1
                  have p1792_3 := h1792c.2.2.2
                  linarith only [hlam, p1792_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1818 | h1818
              · rcases h0bigk with h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c | h1819c
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, hlam, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1082, hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1343, hlam, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1657, hlam, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1819_1, u3ehi0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1819_1, u4ehi0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, h1657, hc01, hc12, hlam, hphi, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1760, hlam, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, h1760, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1819_1, u4ehi0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h0, h1657, h1760, hc01, hc12, hlam, hphi, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1760, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1819_1, u3ehi0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1762, hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1764, hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1761, hlam, p1819_1]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1763, hlam, p1819_0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [h1760, h1763, hc02, hlam, hphi, ht0b, ht45, ht5b, p1819_1, u4ehi0]
                · have p1819_0 := h1819c.1
                  have p1819_1 := h1819c.2.1
                  have p1819_2 := h1819c.2.2.1
                  have p1819_3 := h1819c.2.2.2
                  linarith only [hlam, p1819_0]
              · rcases h0bigk with h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c | h1845c
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, hlam, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1082, hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1343, hlam, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1657, hlam, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, h1763, h1818, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1845_1, u3ehi2]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, h1762, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1845_1, u3ehi3]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, h1657, hc01, hc12, hlam, hphi, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1760, hlam, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, h1760, h1762, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1845_1, u3ehi3]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h0, h1657, h1760, hc01, hc12, hlam, hphi, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1764, hc02, hc45, hlam, hphi, ht23, ht34, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1762, hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1764, hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1761, hlam, p1845_1]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1763, hlam, p1845_0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [h1764, hc45, hlam, hphi, p1845_1, u4ehi0]
                · have p1845_0 := h1845c.1
                  have p1845_1 := h1845c.2.1
                  have p1845_2 := h1845c.2.2.1
                  have p1845_3 := h1845c.2.2.2
                  linarith only [hlam, p1845_0]
          · linarith only [h1762, h1763, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1872 | h1872
          · linarith only [h1762, h1872, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1874 | h1874
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1875 | h1875
              · linarith only [h1760, h1872, h1875, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c | h1877c
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [hlam, p1877_0]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h0, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1082, hlam, p1877_0]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1343, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1657, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [hlam, p1877_0]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h0, h1760, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1, u3ehi2]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h0, h1874, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1877_1, u4ehi4]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h0, h1760, h1872, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1877_1, u3ehi2]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1762, hc01, hc34, hlam, hphi, ht12, ht23, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1760, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [hlam, p1877_0]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1762, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1872, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1762, hc02, hc34, hlam, hphi, ht23, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1762, hc34, hlam, hphi, p1877_1, u3ehi0]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [hlam, p1877_0]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1760, h1762, h1872, hc34, hlam, hphi, p1877_1, u3ehi2]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1761, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1760, h1872, hc35, hlam, hphi, p1877_1, u3ehi2]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [h1874, hlam, p1877_1]
                · have p1877_0 := h1877c.1
                  have p1877_1 := h1877c.2.1
                  have p1877_2 := h1877c.2.2.1
                  have p1877_3 := h1877c.2.2.2
                  linarith only [hlam, p1877_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1903 | h1903
              · linarith only [h1760, h1762, h1903, hc34, hlam, hphi, u3ehi4]
              · rcases h0bigk with h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [hlam, p1905_0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h0, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1082, hlam, p1905_0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1343, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1657, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [hlam, p1905_0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1905_1, u3ehi0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1905_1, u4ehi0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h0, h1657, hc01, hc12, hlam, hphi, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1760, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [hlam, p1905_0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1762, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1872, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1874, hc02, hc45, hlam, hphi, ht23, ht34, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1874, hc45, hlam, hphi, ht34, p1905_1, u3ehi0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [hlam, p1905_0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1874, hlam, p1905_0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1761, hlam, p1905_1]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1760, h1872, hc35, hlam, hphi, p1905_1, u3ehi2]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [h1874, hc45, hlam, hphi, p1905_1, u4ehi0]
                · have p1905_0 := h1905c.1
                  have p1905_1 := h1905c.2.1
                  have p1905_2 := h1905c.2.2.1
                  have p1905_3 := h1905c.2.2.2
                  linarith only [hlam, p1905_0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1931 | h1931
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1932 | h1932
          · linarith only [h1760, h1761, h1932, hlam]
          · linarith only [h1931, h1932, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1935 | h1935
          · linarith only [h1931, h1935, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1937 | h1937
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1938 | h1938
              · linarith only [h1343, h1760, h1761, h1935, h1937, h1938, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h1760, h1761, h1938, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1941 | h1941
              · linarith only [h1760, h1761, h1941, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h1760, h1761, h1941, hc35, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1944 | h1944
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1945 | h1945
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1946 | h1946
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1947 | h1947
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1948 | h1948
              · rcases h0bigk with h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c | h1949c
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h0, hlam, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1082, hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1343, hlam, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1657, hlam, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, hc01, hc23, hlam, hphi, ht12, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1949_1, u4ehi0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1657, h1760, hc01, hc23, hlam, hphi, ht12, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, h1944, h1948, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1949_1, u3ehi4]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1949_1, u4ehi0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, h1944, h1948, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1949_1, u3ehi4]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, h1944, h1945, h1948, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1949_1, u3ehi4]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1945, hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1760, h1944, h1945, h1948, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1949_1, u3ehi4]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1944, hlam, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1946, hlam, p1949_0]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [h1947, hlam, p1949_1]
                · have p1949_0 := h1949c.1
                  have p1949_1 := h1949c.2.1
                  have p1949_2 := h1949c.2.2.1
                  have p1949_3 := h1949c.2.2.2
                  linarith only [hlam, p1949_0]
              · linarith only [h1760, h1945, h1948, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1976 | h1976
              · rcases h0bigk with h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, hlam, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1082, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1343, hlam, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1657, hlam, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, hc01, hc23, hlam, hphi, ht12, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, h1945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1977_1, u3ehi3]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, h1945, h1947, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1977_1, u3ehi3]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, hc02, hc23, hlam, hphi, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, h1945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1977_1, u3ehi3]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, h1945, h1947, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1977_1, u3ehi3]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1947, hc02, hc45, hlam, hphi, ht23, ht34, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1945, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1947, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h0, h1944, hc01, hc12, hlam, hphi, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1944, hlam, p1977_1]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1946, hlam, p1977_0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [h1760, h1944, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1977_1, u4ehi0]
                · have p1977_0 := h1977c.1
                  have p1977_1 := h1977c.2.1
                  have p1977_2 := h1977c.2.2.1
                  have p1977_3 := h1977c.2.2.2
                  linarith only [hlam, p1977_0]
              · linarith only [h1760, h1945, h1976, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1945, h1946, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2005 | h2005
          · linarith only [h1945, h2005, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1760, h1944, h2005, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2008 | h2008
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2009 | h2009
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2010 | h2010
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2011 | h2011
              · rcases h0bigk with h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c | h2012c
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h0, hlam, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1082, hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1343, hlam, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1657, hlam, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1944, h2011, hc01, hc23, hlam, hphi, ht12, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1760, hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1944, h2010, hlam, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1944, hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1760, hc02, hc23, hlam, hphi, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1760, h2010, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2012_1, u4ehi4]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h0, h1760, h1944, hc01, hc23, hlam, hphi, ht12, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h0, h1760, h2008, hc01, hc23, hlam, hphi, ht12, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h2008, hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1760, h2008, h2009, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2012_1, u3ehi4]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h0, h1944, h2011, hc01, hc23, hlam, hphi, ht12, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h2009, hlam, p2012_0]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [h2010, hlam, p2012_1]
                · have p2012_0 := h2012c.1
                  have p2012_1 := h2012c.2.1
                  have p2012_2 := h2012c.2.2.1
                  have p2012_3 := h2012c.2.2.2
                  linarith only [hlam, p2012_0]
              · linarith only [h1760, h2008, h2011, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2039 | h2039
              · rcases h0bigk with h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c | h2040c
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1082, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1343, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1657, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1760, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2008, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2040_1, u3ehi3]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1944, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1760, hc02, hc23, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1760, h2008, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2040_1, u3ehi3]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1657, h1760, hc01, hc23, hlam, hphi, ht12, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, h1343, hc01, hc14, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2008, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2010, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, h1944, h2039, hc01, hc23, hlam, hphi, ht12, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2009, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2010, hc45, hlam, hphi, p2040_1, u4ehi0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
              · linarith only [h1760, h2008, h2039, hc35, hlam, hphi, u3ehi3]
          · linarith only [h2008, h2009, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2068 | h2068
          · linarith only [h2008, h2068, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2070 | h2070
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2071 | h2071
              · rcases h0bigk with h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c | h2072c
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h0, hlam, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1082, hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1343, hlam, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1657, hlam, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1760, hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1760, h2068, h2070, h2071, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2072_1, u4ehi4]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1944, hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2068, h2071, hc01, hc23, hlam, hphi, ht12, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2068, h2071, hc02, hc23, hlam, hphi, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2008, hlam, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2068, hlam, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h0, h2008, hc01, hc34, hlam, hphi, ht12, ht23, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2008, hc34, hlam, hphi, p2072_1, u3ehi0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [hlam, p2072_0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2008, h2068, hc34, hlam, hphi, p2072_1, u3ehi0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h0, h1944, hc01, hc25, hlam, hphi, ht12, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2068, h2071, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2072_1, u3ehi0]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [h2070, hlam, p2072_1]
                · have p2072_0 := h2072c.1
                  have p2072_1 := h2072c.2.1
                  have p2072_2 := h2072c.2.2.1
                  have p2072_3 := h2072c.2.2.2
                  linarith only [hlam, p2072_0]
              · rcases h0bigk with h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h0, hlam, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1082, hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1343, hlam, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1657, hlam, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1760, hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1760, h2071, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2098_1, u4ehi0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1944, hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1760, h2071, hc02, hc35, hlam, hphi, ht23, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h2008, hlam, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h2068, hlam, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h0, h2008, hc01, hc34, hlam, hphi, ht12, ht23, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h2008, hc34, hlam, hphi, p2098_1, u3ehi0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [hlam, p2098_0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1657, h2008, hc01, hc34, hlam, hphi, ht12, ht23, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1657, hc01, hc15, hlam, hphi, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h0, h1944, h2071, hc01, hc35, hlam, hphi, ht12, ht23, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h1944, h2071, hc35, hlam, hphi, p2098_1, u3ehi0]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [h2070, hlam, p2098_1]
                · have p2098_0 := h2098c.1
                  have p2098_1 := h2098c.2.1
                  have p2098_2 := h2098c.2.2.1
                  have p2098_3 := h2098c.2.2.2
                  linarith only [hlam, p2098_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2124 | h2124
              · rcases h0bigk with h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c | h2125c
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h0, hlam, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1082, hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1343, hlam, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1657, hlam, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1760, hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p2125_1, u4ehi0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1944, hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1760, hc02, hc23, hlam, hphi, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2008, hlam, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2068, hlam, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h0, h2070, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2070, hc45, hlam, hphi, ht34, p2125_1, u3ehi0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2070, hlam, p2125_0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2068, h2124, hc01, hc23, hlam, hphi, ht12, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h0, h2068, h2124, hc01, hc23, hlam, hphi, ht12, p2125_1]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2068, h2124, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2125_1, u3ehi0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [h2068, h2124, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2125_1, u4ehi0]
                · have p2125_0 := h2125c.1
                  have p2125_1 := h2125c.2.1
                  have p2125_2 := h2125c.2.2.1
                  have p2125_3 := h2125c.2.2.2
                  linarith only [hlam, p2125_0]
              · rcases h0bigk with h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c | h2151c
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h0, hlam, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1082, hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1343, hlam, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1657, hlam, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1760, hc01, hc23, hlam, hphi, ht12, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1760, hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1760, h2008, h2124, hc35, hlam, hphi, p2151_1, u3ehi0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1944, hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1082, hc01, hc13, hlam, hphi, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1760, h2124, hc02, hc35, hlam, hphi, ht23, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2008, hlam, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2068, hlam, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h1343, hc01, hc14, hlam, hphi, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h0, h2070, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2070, hc45, hlam, hphi, ht34, p2151_1, u3ehi0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2070, hlam, p2151_0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2070, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h0, h2070, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2151_1]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2070, hc45, hlam, hphi, ht34, p2151_1, u3ehi0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [h2070, hc45, hlam, hphi, p2151_1, u4ehi0]
                · have p2151_0 := h2151c.1
                  have p2151_1 := h2151c.2.1
                  have p2151_2 := h2151c.2.2.1
                  have p2151_3 := h2151c.2.2.2
                  linarith only [hlam, p2151_0]

set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1082 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1343 | h1343
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h1082 h1343
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h1082 h1343

set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1082 | h1082
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x0 m hb0 hb1 hb3 hb4 h0 h1082
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x1 m hb0 hb1 hb3 hb4 h0 h1082

end R2N4
