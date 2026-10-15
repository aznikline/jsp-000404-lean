import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S10
import Jsp000404.R1LeavesN7_56S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1362 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1589 | h1589
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1590 | h1590
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1591 | h1591
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1592 | h1592
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1593 | h1593
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1594 | h1594
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1595 | h1595
              · rcases h0bigk with h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, hlam, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1078, hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1362, h1594, hlam, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1362, hlam, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, h1589, h1595, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi4]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, h1362, h1594, hc01, hc12, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, h1362, hc01, hc12, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1589, hlam, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, h1362, h1589, h1594, hc01, hc12, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, h1362, h1589, hc01, hc12, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h0, h1590, hc01, hc12, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1590, hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1592, hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1591, h1595, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1596_1, u3ehi4]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1591, hlam, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1593, hlam, p1596_0]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [h1594, hlam, p1596_1]
                · have p1596_0 := h1596c.1
                  have p1596_1 := h1596c.2.1
                  have p1596_2 := h1596c.2.2.1
                  have p1596_3 := h1596c.2.2.2
                  linarith only [hlam, p1596_0]
              · rcases h0bigk with h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, hlam, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1078, hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1594, hc01, hc45, hlam, hphi, ht0b, ht5b, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1362, hlam, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1622_1, u3ehi0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, h1594, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, h1362, hc01, hc12, hlam, hphi, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1589, hlam, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, h1589, h1594, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, h1589, h1591, h1595, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1622_1, u3ehi2]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h0, h1590, hc01, hc12, hlam, hphi, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1590, hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1592, hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1593, h1595, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1622_1, u3ehi2]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1591, hlam, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1593, hlam, p1622_0]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [h1594, hlam, p1622_1]
                · have p1622_0 := h1622c.1
                  have p1622_1 := h1622c.2.1
                  have p1622_2 := h1622c.2.2.1
                  have p1622_3 := h1622c.2.2.2
                  linarith only [hlam, p1622_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1648 | h1648
              · rcases h0bigk with h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, hlam, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1078, hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1362, hlam, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1649_1, u3ehi0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, h1592, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1649_1, u3ehi3]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, h1362, hc01, hc12, hlam, hphi, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1589, hlam, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, h1589, h1592, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1649_1, u3ehi3]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, h1589, h1591, h1648, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1649_1, u3ehi4]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h0, h1590, hc01, hc12, hlam, hphi, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1590, hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1592, hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1594, hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1591, hlam, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1593, hlam, p1649_0]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [h1594, hc04, hc45, hlam, hphi, p1649_1]
                · have p1649_0 := h1649c.1
                  have p1649_1 := h1649c.2.1
                  have p1649_2 := h1649c.2.2.1
                  have p1649_3 := h1649c.2.2.2
                  linarith only [hlam, p1649_0]
              · rcases h0bigk with h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, hlam, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1078, hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1592, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1675_1, u3ehi3]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1362, hlam, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1675_1, u3ehi0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, h1592, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1675_1, u3ehi3]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, h1362, hc01, hc12, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1589, hlam, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, h1589, h1592, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1675_1, u3ehi3]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, h1362, h1589, hc01, hc12, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h0, h1590, hc01, hc12, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1590, hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1592, hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1594, hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1591, hlam, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1593, hlam, p1675_0]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [h1594, hc04, hc45, hlam, hphi, p1675_1]
                · have p1675_0 := h1675c.1
                  have p1675_1 := h1675c.2.1
                  have p1675_2 := h1675c.2.2.1
                  have p1675_3 := h1675c.2.2.2
                  linarith only [hlam, p1675_0]
          · linarith only [h1592, h1593, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1702 | h1702
          · linarith only [h1592, h1702, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1704 | h1704
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1705 | h1705
              · linarith only [h0, h1589, h1702, h1705, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c | h1707c
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [hlam, p1707_0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h0, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1078, hlam, p1707_0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1589, h1702, h1704, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1707_1, u3ehi2]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1362, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [hlam, p1707_0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h0, h1589, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1707_1, u3ehi2]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h0, h1589, h1702, h1704, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1707_1, u3ehi2]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h0, h1589, h1702, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1707_1, u3ehi2]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1702, hc01, hc35, hlam, hphi, ht12, ht23, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1589, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [hlam, p1707_0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1592, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1702, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h0, h1590, hc01, hc12, hlam, hphi, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1590, hlam, p1707_0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1592, hc34, hlam, hphi, p1707_1, u3ehi0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [hlam, p1707_0]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1589, h1592, h1702, hc34, hlam, hphi, p1707_1, u3ehi2]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1591, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1589, h1702, hc35, hlam, hphi, p1707_1, u3ehi2]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [h1704, hlam, p1707_1]
                · have p1707_0 := h1707c.1
                  have p1707_1 := h1707c.2.1
                  have p1707_2 := h1707c.2.2.1
                  have p1707_3 := h1707c.2.2.2
                  linarith only [hlam, p1707_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1733 | h1733
              · linarith only [h1589, h1592, h1733, hc34, hlam, hphi, u3ehi4]
              · rcases h0bigk with h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h0, hlam, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1078, hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1592, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1735_1, u3ehi0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1362, hlam, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1735_1, u3ehi0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h0, h1589, h1592, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1735_1, u3ehi2]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h0, h1362, hc01, hc12, hlam, hphi, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1589, hlam, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1592, hlam, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1702, hlam, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1704, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1590, hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1704, hc45, hlam, hphi, ht34, p1735_1, u3ehi0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1704, hlam, p1735_0]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1591, hlam, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1589, h1702, hc35, hlam, hphi, p1735_1, u3ehi2]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [h1704, hc04, hc45, hlam, hphi, p1735_1]
                · have p1735_0 := h1735c.1
                  have p1735_1 := h1735c.2.1
                  have p1735_2 := h1735c.2.2.1
                  have p1735_3 := h1735c.2.2.2
                  linarith only [hlam, p1735_0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1761 | h1761
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1762 | h1762
          · linarith only [h1589, h1591, h1762, hlam]
          · linarith only [h1761, h1762, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1765 | h1765
          · linarith only [h1761, h1765, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1767 | h1767
            · linarith only [h1590, h1591, h1767, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1769 | h1769
              · linarith only [h1589, h1591, h1765, h1769, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h1589, h1591, h1769, hc35, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1772 | h1772
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1773 | h1773
        · linarith only [h1589, h1590, h1773, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1775 | h1775
          · linarith only [h1773, h1775, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1777 | h1777
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1778 | h1778
              · linarith only [h1589, h1590, h1775, h1778, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [hlam, p1780_0]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h0, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1078, hlam, p1780_0]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1590, h1772, hc01, hc25, hlam, hphi, ht0b, ht5b, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1362, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1590, hc01, hc24, hlam, hphi, ht12, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [hlam, p1780_0]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1589, h1590, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1780_1, u3ehi2]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1590, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1590, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1589, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [hlam, p1780_0]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1773, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1775, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1590, hc01, hc24, hlam, hphi, ht12, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1772, hc04, hc25, hlam, hphi, ht0b, ht5b, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1773, hc34, hlam, hphi, p1780_1, u3ehi0]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [hlam, p1780_0]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1589, h1773, h1775, hc34, hlam, hphi, p1780_1, u3ehi2]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1772, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1589, h1772, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1780_1, u3ehi2]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [h1777, hlam, p1780_1]
                · have p1780_0 := h1780c.1
                  have p1780_1 := h1780c.2.1
                  have p1780_2 := h1780c.2.2.1
                  have p1780_3 := h1780c.2.2.2
                  linarith only [hlam, p1780_0]
            · linarith only [h1589, h1590, h1777, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1807 | h1807
        · linarith only [h1589, h1590, h1807, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1809 | h1809
          · linarith only [h1807, h1809, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1811 | h1811
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1812 | h1812
              · linarith only [h1589, h1809, h1812, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h1589, h1772, h1812, hc35, hlam, hphi, u3ehi2]
            · linarith only [h1589, h1590, h1811, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1816 | h1816
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1817 | h1817
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1818 | h1818
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1819 | h1819
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1820 | h1820
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1821 | h1821
              · rcases h0bigk with h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h0, hlam, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1078, hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1820, hc01, hc45, hlam, hphi, ht0b, ht5b, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1362, hlam, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, hc01, hc23, hlam, hphi, ht12, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, h1820, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1362, h1589, hc01, hc23, hlam, hphi, ht12, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, h1817, h1821, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1822_1, u3ehi4]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, h1820, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, h1817, h1821, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1822_1, u3ehi4]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h0, h1816, hc01, hc12, hlam, hphi, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1816, hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1818, hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1589, h1816, h1817, h1821, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1822_1, u3ehi4]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1817, hlam, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1819, hlam, p1822_0]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [h1820, hlam, p1822_1]
                · have p1822_0 := h1822c.1
                  have p1822_1 := h1822c.2.1
                  have p1822_2 := h1822c.2.2.1
                  have p1822_3 := h1822c.2.2.2
                  linarith only [hlam, p1822_0]
              · linarith only [h1589, h1818, h1821, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1849 | h1849
              · rcases h0bigk with h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c | h1850c
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h0, hlam, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1078, hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1818, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1850_1, u3ehi3]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1362, hlam, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, hc01, hc23, hlam, hphi, ht12, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, h1818, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1850_1, u3ehi3]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, hc02, hc23, hlam, hphi, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, h1818, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1850_1, u3ehi3]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, h1817, h1849, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1850_1, u3ehi4]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1820, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1816, hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1818, hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1820, hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1817, hlam, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1819, hlam, p1850_0]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [h1589, h1817, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1850_1]
                · have p1850_0 := h1850c.1
                  have p1850_1 := h1850c.2.1
                  have p1850_2 := h1850c.2.2.1
                  have p1850_3 := h1850c.2.2.2
                  linarith only [hlam, p1850_0]
              · linarith only [h1589, h1816, h1818, h1849, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1818, h1819, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1589, h1816, h1818, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1879 | h1879
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1880 | h1880
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1881 | h1881
            · linarith only [h1816, h1817, h1881, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1883 | h1883
              · rcases h0bigk with h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h0, hlam, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1078, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1362, hlam, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1817, hc01, hc25, hlam, hphi, ht12, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1589, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1817, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1817, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1589, hc02, hc23, hlam, hphi, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1589, h1879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1884_1, u3ehi3]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1589, h1816, h1817, h1879, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1884_1, u3ehi3]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1881, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1816, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1879, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1881, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1817, h1883, hc02, hc23, hlam, hphi, p1884_1]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1880, hlam, p1884_0]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [h1879, h1881, hc45, hlam, hphi, ht34, p1884_1, u3ehi3]
                · have p1884_0 := h1884c.1
                  have p1884_1 := h1884c.2.1
                  have p1884_2 := h1884c.2.2.1
                  have p1884_3 := h1884c.2.2.2
                  linarith only [hlam, p1884_0]
              · linarith only [h1589, h1880, h1883, hlam]
          · linarith only [h1879, h1880, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1589, h1816, h1879, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1913 | h1913
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1914 | h1914
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1915 | h1915
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1916 | h1916
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1917 | h1917
              · rcases h0bigk with h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h0, hlam, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1078, hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1816, h1913, h1917, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1918_1, u3ehi4]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1362, hlam, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1816, hc01, hc24, hlam, hphi, ht12, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1589, hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1816, hlam, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1816, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1589, h1913, h1917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1918_1, u3ehi4]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1589, h1816, h1913, h1917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1918_1, u3ehi4]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1589, h1913, h1917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1918_1, u3ehi4]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1816, hc01, hc24, hlam, hphi, ht12, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1913, h1917, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1918_1, u3ehi4]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1914, hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1589, h1913, h1914, h1917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1918_1, u3ehi4]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1913, hlam, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1915, hlam, p1918_0]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [h1916, hlam, p1918_1]
                · have p1918_0 := h1918c.1
                  have p1918_1 := h1918c.2.1
                  have p1918_2 := h1918c.2.2.1
                  have p1918_3 := h1918c.2.2.2
                  linarith only [hlam, p1918_0]
              · linarith only [h1589, h1914, h1917, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1816, h1913, h1916, hlam]
          · linarith only [h1914, h1915, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1947 | h1947
          · linarith only [h1914, h1947, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1589, h1913, h1947, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1950 | h1950
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1951 | h1951
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1952 | h1952
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1953 | h1953
              · rcases h0bigk with h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c | h1954c
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h0, hlam, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1078, hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1952, hc01, hc45, hlam, hphi, ht0b, ht5b, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1362, hlam, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1913, h1953, hc01, hc23, hlam, hphi, ht12, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1589, hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1816, hlam, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1913, hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1589, hc02, hc23, hlam, hphi, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1589, h1952, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h0, h1589, h1913, hc01, hc23, hlam, hphi, ht12, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1816, hc01, hc24, hlam, hphi, ht12, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h0, h1816, hc01, hc24, hlam, hphi, ht12, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1950, hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1589, h1950, h1951, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1954_1, u3ehi4]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h0, h1913, h1953, hc01, hc23, hlam, hphi, ht12, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1951, hlam, p1954_0]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [h1952, hlam, p1954_1]
                · have p1954_0 := h1954c.1
                  have p1954_1 := h1954c.2.1
                  have p1954_2 := h1954c.2.2.1
                  have p1954_3 := h1954c.2.2.2
                  linarith only [hlam, p1954_0]
              · linarith only [h1589, h1950, h1953, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1981 | h1981
              · rcases h0bigk with h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h0, hlam, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1078, hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1362, hlam, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1816, h1913, h1952, hc01, hc25, hlam, hphi, ht12, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1589, hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1816, hlam, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1913, hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1589, hc01, hc23, hlam, hphi, ht12, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1589, hc02, hc23, hlam, hphi, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h0, h1589, h1816, hc01, hc23, hlam, hphi, ht12, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1362, h1589, hc01, hc23, hlam, hphi, ht12, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1362, h1952, hc01, hc15, hlam, hphi, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h0, h1362, h1952, hc01, hc15, hlam, hphi, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1950, hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1952, hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h0, h1913, h1981, hc01, hc23, hlam, hphi, ht12, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h1951, hlam, p1982_0]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [h0, h1816, h1913, h1981, hc01, hc23, hlam, hphi, ht12, p1982_1]
                · have p1982_0 := h1982c.1
                  have p1982_1 := h1982c.2.1
                  have p1982_2 := h1982c.2.2.1
                  have p1982_3 := h1982c.2.2.2
                  linarith only [hlam, p1982_0]
              · linarith only [h1589, h1950, h1981, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1950, h1951, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2010 | h2010
          · linarith only [h1950, h2010, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2012 | h2012
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2013 | h2013
              · rcases h0bigk with h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h0, hlam, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1078, hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h0, h2010, h2012, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p2014_1, u3ehi0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1362, hlam, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1589, hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1816, hlam, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1913, hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h2010, h2013, hc01, hc23, hlam, hphi, ht12, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h2010, h2013, hc02, hc23, hlam, hphi, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1950, hlam, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h2010, hlam, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1816, hc01, hc24, hlam, hphi, ht12, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h0, h1816, hc01, hc24, hlam, hphi, ht12, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1950, hc34, hlam, hphi, p2014_1, u3ehi0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [hlam, p2014_0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1950, h2010, hc34, hlam, hphi, p2014_1, u3ehi0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h0, h1913, hc01, hc25, hlam, hphi, ht12, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h2010, h2013, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2014_1, u3ehi0]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [h2012, hlam, p2014_1]
                · have p2014_0 := h2014c.1
                  have p2014_1 := h2014c.2.1
                  have p2014_2 := h2014c.2.2.1
                  have p2014_3 := h2014c.2.2.2
                  linarith only [hlam, p2014_0]
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
                  linarith only [h1078, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, h2012, hc02, hc45, hlam, hphi, ht0b, ht5b, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1362, hlam, p2040_1]
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
                  linarith only [h1589, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1816, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1913, hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1589, h2013, hc02, hc35, hlam, hphi, ht23, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1950, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2010, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1816, hc01, hc24, hlam, hphi, ht12, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, h1816, hc01, hc24, hlam, hphi, ht12, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1950, hc34, hlam, hphi, p2040_1, u3ehi0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1950, h2010, hc34, hlam, hphi, p2040_1, u3ehi0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1362, hc01, hc15, hlam, hphi, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h0, h1913, h2013, hc01, hc35, hlam, hphi, ht12, ht23, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h1913, h2013, hc35, hlam, hphi, p2040_1, u3ehi0]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [h2012, hlam, p2040_1]
                · have p2040_0 := h2040c.1
                  have p2040_1 := h2040c.2.1
                  have p2040_2 := h2040c.2.2.1
                  have p2040_3 := h2040c.2.2.2
                  linarith only [hlam, p2040_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2066 | h2066
              · rcases h0bigk with h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h0, hlam, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1078, hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1362, hlam, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1589, hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1816, hlam, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1913, hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1589, hc02, hc23, hlam, hphi, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1950, hlam, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h2010, hlam, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1816, hc01, hc24, hlam, hphi, ht12, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h0, h1816, hc01, hc24, hlam, hphi, ht12, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h1950, hc34, hlam, hphi, p2067_1, u3ehi0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h2012, hlam, p2067_0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h2010, h2066, hc01, hc23, hlam, hphi, ht12, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h0, h2010, h2066, hc01, hc23, hlam, hphi, ht12, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h2010, h2066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2067_1, u3ehi0]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [h2010, h2066, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2067_1]
                · have p2067_0 := h2067c.1
                  have p2067_1 := h2067c.2.1
                  have p2067_2 := h2067c.2.2.1
                  have p2067_3 := h2067c.2.2.2
                  linarith only [hlam, p2067_0]
              · rcases h0bigk with h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h0, hlam, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1078, hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1950, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p2093_1, u3ehi0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1362, hlam, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1589, hc01, hc23, hlam, hphi, ht12, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1589, hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1816, hlam, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1913, hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1589, h2066, hc02, hc35, hlam, hphi, ht23, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h1950, hlam, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2010, hlam, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2012, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h0, h2012, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2012, hc45, hlam, hphi, ht34, p2093_1, u3ehi0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2012, hlam, p2093_0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2012, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h0, h2012, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2012, hc45, hlam, hphi, ht34, p2093_1, u3ehi0]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [h2012, hc04, hc45, hlam, hphi, p2093_1]
                · have p2093_0 := h2093c.1
                  have p2093_1 := h2093c.2.1
                  have p2093_2 := h2093c.2.2.1
                  have p2093_3 := h2093c.2.2.2
                  linarith only [hlam, p2093_0]

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1362 | h1362
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1078 h1362
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1078 h1362

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1078 | h1078
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h1078
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h1078

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
