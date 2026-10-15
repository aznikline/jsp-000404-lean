import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1528 | h1528
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1529 | h1529
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1530 | h1530
      · linarith only [h0, h1530, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1532 | h1532
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1533 | h1533
          · linarith only [h1, h1533, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1535 | h1535
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1536 | h1536
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1537 | h1537
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1538 | h1538
                  · linarith only [h0, h1533, h1535, h1537, h1538, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases h0bigk with h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1529, h1535, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1540_1, u5ehi3]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1535, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1540_1, u5ehi3]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h2, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1540_1, u5ehi0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h0, hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1535, hc02, hlam, hphi, ht0b, ht5b, p1540_1, u5ehi3]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1530, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1530, h1536, h1538, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1540_1, u5ehi4]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1529, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1533, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1536, hc03, hlam, hphi, ht0b, ht5b, p1540_1, u5ehi4]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1530, h1538, hc01, hc34, hlam, hphi, ht12, ht23, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1530, h1538, hc02, hc34, hlam, hphi, ht23, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1530, h1538, hc03, hc34, hlam, hphi, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1530, h1536, h1538, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1540_1, u5ehi4]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1528, hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1532, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1535, hlam, p1540_0]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [h1536, hlam, p1540_1]
                    · have p1540_0 := h1540c.1
                      have p1540_1 := h1540c.2.1
                      have p1540_2 := h1540c.2.2.1
                      have p1540_3 := h1540c.2.2.2
                      linarith only [hlam, p1540_0]
                · linarith only [h1529, h1530, h1537, hc12, hc24, hlam, hphi]
              · linarith only [h1528, h1536, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1568 | h1568
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1569 | h1569
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
                  · linarith only [h0, h1569, h1570, h2, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h0bigk with h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [hlam, p1572_0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1532, hc01, hlam, hphi, ht0b, ht5b, p1572_1, u5ehi0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h2, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1572_1, u5ehi0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h0, hlam, p1572_0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [hlam, p1572_0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h0, h1, h1569, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1530, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1528, h1530, h1570, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1572_1, u5ehi1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1529, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [hlam, p1572_0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1533, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1535, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1530, h1570, hc01, hc34, hlam, hphi, ht12, ht23, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1530, h1570, hc02, hc34, hlam, hphi, ht23, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1, h1530, h1569, h1570, hc23, hc34, hlam, hphi, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [hlam, p1572_0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1528, h1530, h1570, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1572_1, u5ehi1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1528, hlam, p1572_0]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1532, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1, h1528, h1569, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [h1568, hlam, p1572_1]
                    · have p1572_0 := h1572c.1
                      have p1572_1 := h1572c.2.1
                      have p1572_2 := h1572c.2.2.1
                      have p1572_3 := h1572c.2.2.2
                      linarith only [hlam, p1572_0]
                · linarith only [h1529, h1530, h1569, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1532, h1568, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1600 | h1600
          · linarith only [h1, h1600, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1602 | h1602
            · linarith only [h1529, h1532, h1602, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1605 | h1605
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1606 | h1606
                  · linarith only [h0, h1600, h1605, h1606, h2, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1, h1605, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h2, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1608_1, u5ehi0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h0, hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1, h1532, h1605, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1530, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1532, hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1529, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1600, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1602, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1530, h1606, hc01, hc34, hlam, hphi, ht12, ht23, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1530, h1606, hc02, hc34, hlam, hphi, ht23, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1, h1530, h1605, h1606, hc23, hc34, hlam, hphi, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1529, h1530, h1532, h1606, hc23, hc34, hlam, hphi, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1528, hlam, p1608_0]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1529, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1, h1528, h1605, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [h1604, hlam, p1608_1]
                    · have p1608_0 := h1608c.1
                      have p1608_1 := h1608c.2.1
                      have p1608_2 := h1608c.2.2.1
                      have p1608_3 := h1608c.2.2.2
                      linarith only [hlam, p1608_0]
                · linarith only [h1529, h1530, h1605, hc12, hc24, hlam, hphi]
              · linarith only [h1528, h1604, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1636 | h1636
      · linarith only [h0, h1636, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1638 | h1638
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1639 | h1639
          · linarith only [h1, h1639, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1641 | h1641
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1642 | h1642
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1643 | h1643
                · linarith only [h1529, h1638, h1643, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1645 | h1645
                  · linarith only [h1529, h1638, h1639, h1645, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h1529, h1638, h1645, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h1, h1529, h1638, h1642, h2, hlam]
            · linarith only [h1529, h1638, h1641, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1650 | h1650
          · linarith only [h1, h1650, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1652 | h1652
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1653 | h1653
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1654 | h1654
                · linarith only [h0, h1529, h1654, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1656 | h1656
                  · linarith only [h1650, h1652, h1656, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases h0bigk with h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c | h1658c
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1652, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1658_1, u5ehi3]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h2, hlam, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p1658_1, u5ehi0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h0, hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1529, hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1636, hlam, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1638, hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1, hlam, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1650, hlam, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1528, h1529, h1656, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1658_1, u5ehi1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h0, h1636, hc12, hc24, hlam, hphi, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1650, hc03, hc34, hlam, hphi, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1528, h1650, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1658_1, u5ehi1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1528, hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h0, h1528, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1652, hlam, p1658_0]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [h1653, hlam, p1658_1]
                    · have p1658_0 := h1658c.1
                      have p1658_1 := h1658c.2.1
                      have p1658_2 := h1658c.2.2.1
                      have p1658_3 := h1658c.2.2.2
                      linarith only [hlam, p1658_0]
              · linarith only [h1, h1652, h1653, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1685 | h1685
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1686 | h1686
                · linarith only [h0, h1529, h1686, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1688 | h1688
                  · rcases h0bigk with h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h0, h1650, h1688, h2, hc12, hc23, hlam, hphi, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h0, h1529, h1650, h1688, h2, hc12, hc23, hlam, hphi, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h2, hlam, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1650, h1688, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1689_1, u5ehi0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h0, hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1529, hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1636, hlam, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1638, hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1, hlam, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h0, h1, h1650, h1688, h2, hc12, hc23, hlam, hphi, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1650, hlam, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1652, hlam, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1650, h1688, hc01, hc23, hlam, hphi, ht12, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h0, h1650, h1688, hc12, hc23, hlam, hphi, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1650, h1688, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1528, h1650, h1688, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1689_1, u5ehi1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1528, hlam, p1689_0]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h0, h1528, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1, h1528, h1650, h1686, h1688, h2, hc12, hc23, hlam, hphi, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [h1685, hlam, p1689_1]
                    · have p1689_0 := h1689c.1
                      have p1689_1 := h1689c.2.1
                      have p1689_2 := h1689c.2.2.1
                      have p1689_3 := h1689c.2.2.2
                      linarith only [hlam, p1689_0]
                  · rcases h0bigk with h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h0, h1636, h2, hc12, hc24, hlam, hphi, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1, h1636, h1686, h1688, h2, hc12, hc34, hlam, hphi, ht23, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h2, hlam, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1636, h1688, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1715_1, u5ehi0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h0, hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1529, hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1636, hlam, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1638, hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1, hlam, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1650, hlam, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1652, hlam, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1636, h1688, hc01, hc34, hlam, hphi, ht12, ht23, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h0, h1636, h1688, hc12, hc34, hlam, hphi, ht23, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1636, h1688, hc03, hc34, hlam, hphi, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1528, h1636, h1688, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1715_1, u5ehi1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1528, hlam, p1715_0]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h0, h1528, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1, h1528, h1686, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [h1685, hlam, p1715_1]
                    · have p1715_0 := h1715c.1
                      have p1715_1 := h1715c.2.1
                      have p1715_2 := h1715c.2.2.1
                      have p1715_3 := h1715c.2.2.2
                      linarith only [hlam, p1715_0]
              · linarith only [h1528, h1685, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1742 | h1742
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1743 | h1743
      · linarith only [h0, h1743, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1745 | h1745
        · linarith only [h0, h1528, h1745, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1747 | h1747
          · linarith only [h1, h1747, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1749 | h1749
            · linarith only [h1, h1528, h1749, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1751 | h1751
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1752 | h1752
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1753 | h1753
                  · linarith only [h0, h1752, h1753, h2, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h0bigk with h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [hlam, p1755_0]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h2, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1528, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h0, hlam, p1755_0]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [hlam, p1755_0]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1, h1745, h1752, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1743, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1745, hlam, p1755_0]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1742, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [hlam, p1755_0]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1747, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1749, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1743, h1753, hc02, hc34, hlam, hphi, ht23, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1, h1743, h1752, h1753, hc23, hc34, hlam, hphi, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [hlam, p1755_0]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h0, h1528, h1743, h1753, hc12, hc34, hlam, hphi, ht23, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1742, h1749, hc23, hc35, hlam, hphi, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1, h1749, h1752, hc23, hc35, hlam, hphi, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [h1751, hlam, p1755_1]
                    · have p1755_0 := h1755c.1
                      have p1755_1 := h1755c.2.1
                      have p1755_2 := h1755c.2.2.1
                      have p1755_3 := h1755c.2.2.2
                      linarith only [hlam, p1755_0]
                · linarith only [h1742, h1743, h1752, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1782 | h1782
                · linarith only [h0, h1751, h1782, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1742, h1751, h1782, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1785 | h1785
      · linarith only [h1, h1742, h1785, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1787 | h1787
        · linarith only [h1, h1528, h1742, h1787, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1789 | h1789
          · linarith only [h1, h1789, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1791 | h1791
            · linarith only [h1, h1528, h1791, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1793 | h1793
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                · linarith only [h0, h1742, h1794, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1796 | h1796
                  · rcases h0bigk with h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c | h1797c
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h0, h1528, h1789, h1793, h1796, hc12, hc23, hlam, hphi, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1528, h1789, h1793, h1796, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h2, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1528, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h0, hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1742, hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1785, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1787, hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h0, h1791, hc12, hc35, hlam, hphi, ht23, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1789, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1791, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1789, h1796, hc01, hc23, hlam, hphi, ht12, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h0, h1789, h1796, hc12, hc23, hlam, hphi, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1789, h1796, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [hlam, p1797_0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1789, h1796, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1797_1, u5ehi0]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1, h1794, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h0, h1787, hc12, hc25, hlam, hphi, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1, h1791, h1794, hc12, hc35, hlam, hphi, ht23, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [h1793, hlam, p1797_1]
                    · have p1797_0 := h1797c.1
                      have p1797_1 := h1797c.2.1
                      have p1797_2 := h1797c.2.2.1
                      have p1797_3 := h1797c.2.2.2
                      linarith only [hlam, p1797_0]
                  · rcases h0bigk with h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c | h1823c
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1, h1794, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h2, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1528, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h0, hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1742, hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1785, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1787, hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1789, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1791, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h2, hc01, hc14, hlam, hphi, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h0, h1785, hc12, hc24, hlam, hphi, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1789, hc03, hc34, hlam, hphi, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [hlam, p1823_0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1789, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1823_1, u5ehi0]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1, h1794, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h0, h1787, hc12, hc25, hlam, hphi, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1, h1791, h1794, hc12, hc35, hlam, hphi, ht23, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [h1793, hlam, p1823_1]
                    · have p1823_0 := h1823c.1
                      have p1823_1 := h1823c.2.1
                      have p1823_2 := h1823c.2.2.1
                      have p1823_3 := h1823c.2.2.2
                      linarith only [hlam, p1823_0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1849 | h1849
                · linarith only [h0, h1793, h1849, h2, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1851 | h1851
                  · rcases h0bigk with h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h0, h1789, h1851, h2, hc12, hc23, hlam, hphi, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h0, h1742, h1789, h1851, h2, hc12, hc23, hlam, hphi, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h2, hlam, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1528, hlam, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h0, hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1742, hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1785, hlam, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1787, hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1, hlam, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h0, h1, h1789, h1851, h2, hc12, hc23, hlam, hphi, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1789, hlam, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1791, hlam, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1789, h1851, hc01, hc23, hlam, hphi, ht12, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h0, h1789, h1851, hc12, hc23, hlam, hphi, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1789, h1851, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1793, hlam, p1852_0]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h0, h1793, hc12, hc45, hlam, hphi, ht23, ht34, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1, h1793, h1849, hc12, hc45, hlam, hphi, ht23, ht34, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [h1793, hc04, hc45, hlam, hphi, p1852_1]
                    · have p1852_0 := h1852c.1
                      have p1852_1 := h1852c.2.1
                      have p1852_2 := h1852c.2.2.1
                      have p1852_3 := h1852c.2.2.2
                      linarith only [hlam, p1852_0]
                  · rcases h0bigk with h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c | h1878c
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1, h1849, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h2, hlam, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1528, hlam, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h0, hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1742, hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1785, hlam, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1787, hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1, hlam, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1789, hlam, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1791, hlam, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h0, h1785, h1851, hc12, hc34, hlam, hphi, ht23, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1785, h1851, hc03, hc34, hlam, hphi, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1793, hlam, p1878_0]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h0, h1793, hc12, hc45, hlam, hphi, ht23, ht34, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1, h1793, h1849, hc12, hc45, hlam, hphi, ht23, ht34, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [h1793, hc04, hc45, hlam, hphi, p1878_1]
                    · have p1878_0 := h1878c.1
                      have p1878_1 := h1878c.2.1
                      have p1878_2 := h1878c.2.2.1
                      have p1878_3 := h1878c.2.2.2
                      linarith only [hlam, p1878_0]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

end R2N4
