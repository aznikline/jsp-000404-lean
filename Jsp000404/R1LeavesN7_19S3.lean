import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h1492 | h1492
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1493 | h1493
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1494 | h1494
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1495 | h1495
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1496 | h1496
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1497 | h1497
            · linarith only [h1497, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1499 | h1499
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1500 | h1500
                · linarith only [h1493, h1500, h2, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1502 | h1502
                  · linarith only [h1492, h1499, h1502, h6, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h1bigk with h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1492, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1496, hc01, hc35, hlam, hphi, ht0b, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      rcases p1504_3 (m.d 0 1) (by simp) with h1508 | h1508
                      · rcases p1504_3 (m.d 1 2) (by simp) with h1509 | h1509
                        · linarith only [h0, h1509, hlam]
                        · linarith only [h1493, h1509, hlam]
                      · linarith only [h1508, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      rcases p1504_3 (m.d 0 1) (by simp) with h1513 | h1513
                      · rcases p1504_3 (m.d 1 2) (by simp) with h1514 | h1514
                        · linarith only [h0, h1514, hlam]
                        · linarith only [h1494, h1514, hlam]
                      · linarith only [h1513, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1492, h1499, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1493, h1499, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1492, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1, h1493, h1499, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1492, h1494, hc01, hc25, hlam, hphi, ht0b, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h2, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1493, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1495, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1497, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h3, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1494, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1496, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1493, h1499, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1538 | h1538
                · linarith only [h1495, h1499, h1538, h2, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1540 | h1540
                  · linarith only [h1495, h1540, h2, h6, hlam]
                  · rcases h1bigk with h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1492, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1495, h1499, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1495, h1499, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1496, h1499, h1540, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h0, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1496, h1499, h1540, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h0, h1495, h1499, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1492, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1495, h1499, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h0, h1492, h1494, h1538, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h2, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1493, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1495, hlam, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1497, hlam, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h3, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1494, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1496, hlam, p1542_0]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [h1495, h1499, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1542_1]
                    · have p1542_0 := h1542c.1
                      have p1542_1 := h1542c.2.1
                      have p1542_2 := h1542c.2.2.1
                      have p1542_3 := h1542c.2.2.2
                      linarith only [hlam, p1542_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1568 | h1568
            · linarith only [h1568, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1571 | h1571
                · linarith only [h1571, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1573 | h1573
                  · linarith only [h1492, h1570, h1573, h6, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h1bigk with h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1492, h1570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1492, h1570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      rcases p1575_3 (m.d 0 1) (by simp) with h1579 | h1579
                      · rcases p1575_3 (m.d 1 2) (by simp) with h1580 | h1580
                        · linarith only [h0, h1580, hlam]
                        · linarith only [h1493, h1580, hlam]
                      · linarith only [h1579, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1492, h1496, h1570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h0, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1492, h1570, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h0, h1493, h1570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h0, h1492, h1496, h1570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1492, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1493, h1496, h1570, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1496, hlam, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h2, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1493, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1495, hlam, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1568, hlam, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h3, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1494, hlam, p1575_0]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [h1493, h1570, h3, h6, hc34, hc45, hlam, hphi, p1575_1]
                    · have p1575_0 := h1575c.1
                      have p1575_1 := h1575c.2.1
                      have p1575_2 := h1575c.2.2.1
                      have p1575_3 := h1575c.2.2.2
                      linarith only [hlam, p1575_0]
              · linarith only [h1495, h1496, h1570, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1606 | h1606
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1607 | h1607
            · linarith only [h1495, h1606, h1607, h5, h6, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1495, h1606, h1607, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1610 | h1610
            · linarith only [h1610, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1612 | h1612
              · linarith only [h0, h1492, h1495, h1612, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1614 | h1614
                · linarith only [h1493, h1495, h1614, h5, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1616 | h1616
                  · linarith only [h1616, h5, h6, hlam]
                  · rcases h1bigk with h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1492, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      rcases p1618_3 (m.d 0 1) (by simp) with h1621 | h1621
                      · rcases p1618_3 (m.d 1 2) (by simp) with h1622 | h1622
                        · linarith only [h0, h1622, hlam]
                        · linarith only [h1492, h1622, hlam]
                      · linarith only [h1621, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      rcases p1618_3 (m.d 0 1) (by simp) with h1626 | h1626
                      · rcases p1618_3 (m.d 1 2) (by simp) with h1627 | h1627
                        · linarith only [h0, h1627, hlam]
                        · linarith only [h1493, h1627, hlam]
                      · linarith only [h1626, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      rcases p1618_3 (m.d 0 1) (by simp) with h1631 | h1631
                      · rcases p1618_3 (m.d 1 2) (by simp) with h1632 | h1632
                        · linarith only [h0, h1632, hlam]
                        · linarith only [h1494, h1632, hlam]
                      · linarith only [h1631, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, h1492, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1492, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1495, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1606, hlam, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h2, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1493, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1492, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1610, hlam, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h3, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1494, hlam, p1618_0]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h1492, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [h0, h1494, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1618_1]
                    · have p1618_0 := h1618c.1
                      have p1618_1 := h1618c.2.1
                      have p1618_2 := h1618c.2.2.1
                      have p1618_3 := h1618c.2.2.2
                      linarith only [hlam, p1618_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1656 | h1656
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1657 | h1657
          · linarith only [h1492, h1494, h1657, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1659 | h1659
            · linarith only [h1659, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1661 | h1661
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1662 | h1662
                · linarith only [h0, h1492, h1494, h1661, h1662, h3, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1492, h1494, h1661, h1662, hc34, hc45, hlam, hphi]
              · linarith only [h1656, h1657, h1661, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1666 | h1666
          · linarith only [h1492, h1494, h1656, h1666, h5, h6, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1668 | h1668
            · linarith only [h0, h1493, h1656, h1668, h5, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1670 | h1670
              · linarith only [h1492, h1656, h1670, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1672 | h1672
                · linarith only [h1672, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1674 | h1674
                  · linarith only [h1674, h5, h6, hlam]
                  · rcases h1bigk with h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1493, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      rcases p1676_3 (m.d 0 1) (by simp) with h1679 | h1679
                      · rcases p1676_3 (m.d 1 2) (by simp) with h1680 | h1680
                        · linarith only [h0, h1680, hlam]
                        · linarith only [h1492, h1680, hlam]
                      · linarith only [h1679, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      rcases p1676_3 (m.d 0 1) (by simp) with h1684 | h1684
                      · rcases p1676_3 (m.d 1 2) (by simp) with h1685 | h1685
                        · linarith only [h0, h1685, hlam]
                        · linarith only [h1493, h1685, hlam]
                      · linarith only [h1684, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1493, h1494, h1670, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h0, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h0, h1492, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1494, hlam, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1492, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1656, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1666, hlam, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h2, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1493, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1492, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1668, hlam, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h3, hlam, p1676_0]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1493, h1670, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h1492, h3, h6, hc23, hc45, hlam, hphi, ht34, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [h3, h6, hc14, hc45, hlam, hphi, p1676_1]
                    · have p1676_0 := h1676c.1
                      have p1676_1 := h1676c.2.1
                      have p1676_2 := h1676c.2.2.1
                      have p1676_3 := h1676c.2.2.2
                      linarith only [hlam, p1676_0]
    · linarith only [h1492, h1493, h4, h6, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1711 | h1711
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1712 | h1712
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1713 | h1713
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1714 | h1714
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1715 | h1715
            · linarith only [h1715, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1717 | h1717
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1718 | h1718
                · linarith only [h1492, h1711, h1718, h2, h6, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1720 | h1720
                  · linarith only [h1711, h1717, h1720, h2, h6, hlam]
                  · rcases h1bigk with h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1711, h1717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1492, h1711, h1717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      rcases p1722_3 (m.d 0 1) (by simp) with h1726 | h1726
                      · rcases p1722_3 (m.d 1 2) (by simp) with h1727 | h1727
                        · linarith only [h0, h1727, hlam]
                        · linarith only [h1711, h1727, hlam]
                      · linarith only [h1726, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      rcases p1722_3 (m.d 0 1) (by simp) with h1731 | h1731
                      · rcases p1722_3 (m.d 1 2) (by simp) with h1732 | h1732
                        · linarith only [h0, h1732, hlam]
                        · linarith only [h1712, h1732, hlam]
                      · linarith only [h1731, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h0, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1492, hlam, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h0, h1711, h1717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1492, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1, h1711, h1717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1, h1712, h1717, h1718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h2, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1711, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1713, hlam, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1715, hlam, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h3, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1712, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1714, hlam, p1722_0]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [h1711, h1717, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1]
                    · have p1722_0 := h1722c.1
                      have p1722_1 := h1722c.2.1
                      have p1722_2 := h1722c.2.2.1
                      have p1722_3 := h1722c.2.2.2
                      linarith only [hlam, p1722_0]
              · linarith only [h1, h1492, h1712, h1717, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1492, h1712, h1714, hlam]
        · linarith only [h1492, h1711, h1713, h5, h6, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1759 | h1759
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1760 | h1760
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1761 | h1761
            · linarith only [h1761, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1763 | h1763
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1764 | h1764
                · linarith only [h1711, h1712, h1764, h3, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1766 | h1766
                  · linarith only [h1711, h1712, h1763, h1764, h1766, hlam]
                  · rcases h1bigk with h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c | h1768c
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1711, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1711, h1712, h1760, h1763, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      rcases p1768_3 (m.d 0 1) (by simp) with h1772 | h1772
                      · rcases p1768_3 (m.d 1 2) (by simp) with h1773 | h1773
                        · linarith only [h0, h1773, hlam]
                        · linarith only [h1711, h1773, hlam]
                      · linarith only [h1772, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1711, h1712, h1763, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h0, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1492, hlam, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1492, h1711, h1763, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1712, hlam, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1, h1711, h1763, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1, h1711, h1712, h1763, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h2, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1711, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1759, hlam, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1761, hlam, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h3, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1711, h1763, h3, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1760, hlam, p1768_0]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [h1711, h1763, h3, h6, hc34, hc45, hlam, hphi, p1768_1]
                    · have p1768_0 := h1768c.1
                      have p1768_1 := h1768c.2.1
                      have p1768_2 := h1768c.2.2.1
                      have p1768_3 := h1768c.2.2.2
                      linarith only [hlam, p1768_0]
              · linarith only [h1492, h1711, h1763, h5, h6, hc24, hc45, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1799 | h1799
            · linarith only [h1799, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1801 | h1801
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1802 | h1802
                · linarith only [h1492, h1711, h1802, h2, h6, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1804 | h1804
                  · linarith only [h1711, h1712, h1801, h1802, h1804, hlam]
                  · rcases h1bigk with h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1711, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1492, h1711, h1801, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      rcases p1806_3 (m.d 0 1) (by simp) with h1810 | h1810
                      · rcases p1806_3 (m.d 1 2) (by simp) with h1811 | h1811
                        · linarith only [h0, h1811, hlam]
                        · linarith only [h1711, h1811, hlam]
                      · linarith only [h1810, hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1492, h1711, h1760, h1801, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h0, hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1492, hlam, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1492, h1711, h1801, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1712, hlam, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1, hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1760, hc12, hc35, hlam, hphi, ht23, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1711, h1760, h1801, h1804, hc34, hc45, hlam, hphi, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1760, hlam, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h2, hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1711, hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1759, hlam, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1799, hlam, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h3, hlam, p1806_0]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1711, h1801, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [h1711, h1801, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1806_1]
                    · have p1806_0 := h1806c.1
                      have p1806_1 := h1806c.2.1
                      have p1806_2 := h1806c.2.2.1
                      have p1806_3 := h1806c.2.2.2
                      linarith only [hlam, p1806_0]
              · linarith only [h1, h1492, h1711, h1801, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1492, h1711, h1759, h5, h6, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1838 | h1838
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1839 | h1839
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1840 | h1840
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1841 | h1841
            · linarith only [h1711, h1838, h1841, h4, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1711, h1838, h1841, hlam]
          · linarith only [h1711, h1838, h1839, h1840, h4, h6, hc34, hc45, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1845 | h1845
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1846 | h1846
            · linarith only [h1492, h1838, h1839, h1846, h5, h6, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1711, h1838, h1846, hlam]
          · linarith only [h1492, h1838, h1845, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1850 | h1850
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1851 | h1851
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1852 | h1852
            · linarith only [h1852, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1854 | h1854
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1855 | h1855
                · linarith only [h1855, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1857 | h1857
                  · linarith only [h1, h1850, h1857, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h1bigk with h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      rcases p1859_3 (m.d 0 1) (by simp) with h1861 | h1861
                      · rcases p1859_3 (m.d 1 2) (by simp) with h1862 | h1862
                        · linarith only [h1862, hlam, p1859_0]
                        · rcases p1859_3 (m.d 1 3) (by simp) with h1864 | h1864
                          · linarith only [h1, h1864, hlam]
                          · linarith only [h1492, h1864, hlam]
                      · linarith only [h1861, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1850, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      rcases p1859_3 (m.d 0 1) (by simp) with h1869 | h1869
                      · rcases p1859_3 (m.d 1 2) (by simp) with h1870 | h1870
                        · linarith only [h0, h1870, hlam]
                        · rcases p1859_3 (m.d 1 3) (by simp) with h1872 | h1872
                          · linarith only [h1, h1872, hlam]
                          · linarith only [h1850, h1872, hlam]
                      · linarith only [h1869, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      rcases p1859_3 (m.d 0 1) (by simp) with h1876 | h1876
                      · rcases p1859_3 (m.d 1 2) (by simp) with h1877 | h1877
                        · linarith only [h0, h1877, hlam]
                        · rcases p1859_3 (m.d 1 3) (by simp) with h1879 | h1879
                          · linarith only [h1, h1879, hlam]
                          · linarith only [h1851, h1879, hlam]
                      · linarith only [h1876, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h0, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1492, hlam, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1711, hlam, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1838, hlam, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h2, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1850, hlam, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1852, hlam, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h3, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h1851, hlam, p1859_0]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [h3, h6, hc14, hc45, hlam, hphi, p1859_1]
                    · have p1859_0 := h1859c.1
                      have p1859_1 := h1859c.2.1
                      have p1859_2 := h1859c.2.2.1
                      have p1859_3 := h1859c.2.2.2
                      linarith only [hlam, p1859_0]
              · linarith only [h1492, h1854, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
            · linarith only [h1904, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1906 | h1906
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1907 | h1907
                · linarith only [h1907, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1909 | h1909
                  · linarith only [h1711, h1850, h1909, h4, h6, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h1bigk with h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c | h1911c
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      rcases p1911_3 (m.d 0 1) (by simp) with h1913 | h1913
                      · rcases p1911_3 (m.d 1 2) (by simp) with h1914 | h1914
                        · linarith only [h1914, hlam, p1911_0]
                        · rcases p1911_3 (m.d 1 3) (by simp) with h1916 | h1916
                          · linarith only [h1, h1916, hlam]
                          · linarith only [h1492, h1916, hlam]
                      · linarith only [h1913, hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1850, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      rcases p1911_3 (m.d 0 1) (by simp) with h1921 | h1921
                      · rcases p1911_3 (m.d 1 2) (by simp) with h1922 | h1922
                        · linarith only [h0, h1922, hlam]
                        · rcases p1911_3 (m.d 1 3) (by simp) with h1924 | h1924
                          · linarith only [h1, h1924, hlam]
                          · linarith only [h1850, h1924, hlam]
                      · linarith only [h1921, hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1850, h1851, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h0, hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1492, hlam, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1711, hlam, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1838, hlam, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1, hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1851, hlam, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h2, hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1850, hlam, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h1904, hlam, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h3, hlam, p1911_0]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h3, h6, hc13, hc45, hlam, hphi, ht34, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [h3, h6, hc14, hc45, hlam, hphi, p1911_1]
                    · have p1911_0 := h1911c.1
                      have p1911_1 := h1911c.2.1
                      have p1911_2 := h1911c.2.2.1
                      have p1911_3 := h1911c.2.2.2
                      linarith only [hlam, p1911_0]
              · linarith only [h1, h1492, h1850, h1906, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1950 | h1950
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1951 | h1951
            · linarith only [h1850, h1950, h1951, h5, h6, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1850, h1950, h1951, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1954 | h1954
            · linarith only [h1954, h2, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1956 | h1956
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1957 | h1957
                · linarith only [h1957, h4, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1959 | h1959
                  · linarith only [h1956, h1959, h4, h6, hlam]
                  · rcases h1bigk with h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c | h1961c
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      rcases p1961_3 (m.d 0 1) (by simp) with h1963 | h1963
                      · rcases p1961_3 (m.d 1 2) (by simp) with h1964 | h1964
                        · linarith only [h1964, hlam, p1961_0]
                        · rcases p1961_3 (m.d 1 3) (by simp) with h1966 | h1966
                          · linarith only [h1, h1966, hlam]
                          · linarith only [h1492, h1966, hlam]
                      · linarith only [h1963, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      rcases p1961_3 (m.d 0 1) (by simp) with h1970 | h1970
                      · rcases p1961_3 (m.d 1 2) (by simp) with h1971 | h1971
                        · linarith only [h0, h1971, hlam]
                        · rcases p1961_3 (m.d 1 3) (by simp) with h1973 | h1973
                          · linarith only [h1973, hlam, p1961_0]
                          · rcases p1961_3 (m.d 1 4) (by simp) with h1975 | h1975
                            · linarith only [h1975, h2, hlam]
                            · linarith only [h1850, h1975, hlam]
                      · linarith only [h1970, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      rcases p1961_3 (m.d 0 1) (by simp) with h1979 | h1979
                      · rcases p1961_3 (m.d 1 2) (by simp) with h1980 | h1980
                        · linarith only [h0, h1980, hlam]
                        · rcases p1961_3 (m.d 1 3) (by simp) with h1982 | h1982
                          · linarith only [h1, h1982, hlam]
                          · rcases p1961_3 (m.d 1 4) (by simp) with h1984 | h1984
                            · linarith only [h1984, hlam, p1961_0]
                            · rcases p1961_3 (m.d 1 5) (by simp) with h1986 | h1986
                              · linarith only [h1986, h3, hlam]
                              · linarith only [h1954, h1986, hlam]
                      · linarith only [h1979, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      rcases p1961_3 (m.d 0 1) (by simp) with h1990 | h1990
                      · rcases p1961_3 (m.d 1 2) (by simp) with h1991 | h1991
                        · linarith only [h0, h1991, hlam]
                        · rcases p1961_3 (m.d 1 3) (by simp) with h1993 | h1993
                          · linarith only [h1, h1993, hlam]
                          · rcases p1961_3 (m.d 1 4) (by simp) with h1995 | h1995
                            · linarith only [h1995, h2, hlam]
                            · rcases p1961_3 (m.d 1 5) (by simp) with h1997 | h1997
                              · linarith only [h1997, hlam, p1961_0]
                              · rcases h4bigk with h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c | h1999c
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h6, hc14, hc45, hlam, hphi, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1492, h1850, h1956, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1492, h1850, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h6, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h2, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1711, hlam, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1850, hlam, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1954, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h4, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h4, h6, hc14, hc45, hlam, hphi, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1492, h1850, h4, h6, hc12, hc45, hlam, hphi, ht23, ht34, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1957, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h5, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1492, h1850, h1956, hc12, hc23, hlam, hphi, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1956, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1959, hlam, p1999_0]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1711, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  rcases p1999_3 (m.d 0 4) (by simp) with h2021 | h2021
                                  · linarith only [h2021, h6, hlam]
                                  · linarith only [h2, h2021, hlam]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1492, h1850, h1956, hc12, hc45, hlam, hphi, ht23, ht34, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [h1492, h1850, hc12, hc45, hlam, hphi, ht23, ht34, p1999_1]
                                · have p1999_0 := h1999c.1
                                  have p1999_1 := h1999c.2.1
                                  have p1999_2 := h1999c.2.2.1
                                  have p1999_3 := h1999c.2.2.2
                                  linarith only [hlam, p1999_0]
                      · linarith only [h1990, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h0, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1492, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1711, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1838, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1850, h1956, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1850, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1950, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h2, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1850, h1956, h4, h6, hc13, hc45, hlam, hphi, ht34, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1954, hlam, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h3, hlam, p1961_0]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h1492, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1961_1]
                    · have p1961_0 := h1961c.1
                      have p1961_1 := h1961c.2.1
                      have p1961_2 := h1961c.2.2.1
                      have p1961_3 := h1961c.2.2.2
                      linarith only [hlam, p1961_0]
              · linarith only [h1492, h1956, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_21_14_H_I_L_I_s4_x0_x0 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5 h6
  · exact r1l7_21_14_H_I_L_I_s4_x0_x1 m hb1 hb4 hg0 hg1 hg2 hg3 hg4 h5 h6

end R2N4
