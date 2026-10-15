import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1531 | h1531
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1532 | h1532
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1533 | h1533
      · linarith only [h0, h1, h1533, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1535 | h1535
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1536 | h1536
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1537 | h1537
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1538 | h1538
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1540 | h1540
                  · linarith only [h1, h1531, h1540, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1533, h1535, h1539, h1540, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1543 | h1543
                  · linarith only [h1, h1531, h1539, h1543, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1545 | h1545
                    · linarith only [h1537, h1539, h1545, hlam]
                    · rcases h0bigk with h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1547_1, u4ehi0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1, h1537, h1539, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1547_1, u4ehi3]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1533, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1537, hc02, hlam, hphi, ht0b, ht45, ht5b, p1547_1, u4ehi3]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1533, h1537, h1539, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1, u4ehi3]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1533, hc02, hc23, hlam, hphi, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1533, h1537, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1, u4ehi3]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1533, h1537, h1539, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1, u4ehi3]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1531, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1535, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1537, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1539, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1532, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1536, hlam, p1547_1]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1538, hlam, p1547_0]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [h1537, hc05, hlam, hphi, ht0b, ht45, ht5b, p1547_1, u4ehi3]
                      · have p1547_0 := h1547c.1
                        have p1547_1 := h1547c.2.1
                        have p1547_2 := h1547c.2.2.1
                        have p1547_3 := h1547c.2.2.2
                        linarith only [hlam, p1547_0]
              · linarith only [h0, h1, h1536, h1538, hlam]
            · linarith only [h1, h1531, h1537, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1575 | h1575
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1576 | h1576
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1577 | h1577
                · linarith only [h1535, h1536, h1577, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1579 | h1579
                  · linarith only [h1531, h1577, h1579, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1581 | h1581
                    · linarith only [h1535, h1536, h1575, h1577, h1581, hlam]
                    · rcases h0bigk with h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c | h1583c
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1583_1]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1583_1, u4ehi0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h0, h1, h1536, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1583_1]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h0, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1533, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1575, hc02, hlam, hphi, ht0b, ht45, ht5b, p1583_1, u4ehi3]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1536, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1533, hc01, hc23, hlam, hphi, ht12, p1583_1]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1533, hc02, hc23, hlam, hphi, p1583_1]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1533, h1575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1583_1, u4ehi3]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1533, h1535, h1536, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1583_1, u4ehi2]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1531, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1535, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1575, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1577, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1532, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1532, h1535, hc01, hlam, hphi, ht0b, ht45, ht5b, p1583_1, u4ehi2]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1576, hlam, p1583_0]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [h1, h1532, h1575, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1583_1, u4ehi3]
                      · have p1583_0 := h1583c.1
                        have p1583_1 := h1583c.2.1
                        have p1583_2 := h1583c.2.2.1
                        have p1583_3 := h1583c.2.2.2
                        linarith only [hlam, p1583_0]
              · linarith only [h1, h1532, h1576, hlam]
            · linarith only [h1, h1531, h1575, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1611 | h1611
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1612 | h1612
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1613 | h1613
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1614 | h1614
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1615 | h1615
                  · linarith only [h1, h1531, h1615, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1, h1531, h1614, h1615, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h1535, h1611, h1614, hlam]
              · linarith only [h0, h1, h1611, h1613, hlam]
            · linarith only [h1, h1531, h1612, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1621 | h1621
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1622 | h1622
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1623 | h1623
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1624 | h1624
                  · linarith only [h1, h1531, h1624, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1, h1531, h1623, h1624, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1627 | h1627
                  · linarith only [h1, h1531, h1535, h1623, h1627, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1629 | h1629
                    · linarith only [h1621, h1623, h1629, hlam]
                    · rcases h0bigk with h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1631_1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1, h1531, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1631_1, u4ehi1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1, h1531, h1623, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1631_1, u4ehi1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h0, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1533, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1535, hlam, p1631_1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1611, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1631_1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h0, h1533, hc12, hc23, hlam, hphi, p1631_1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1531, h1533, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1631_1, u4ehi1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1531, h1533, h1623, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1631_1, u4ehi1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1531, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h0, h1623, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1621, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1623, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1532, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h0, h1, h1532, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1631_1]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1622, hlam, p1631_0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [h1, h1532, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1631_1, u4ehi0]
                      · have p1631_0 := h1631c.1
                        have p1631_1 := h1631c.2.1
                        have p1631_2 := h1631c.2.2.1
                        have p1631_3 := h1631c.2.2.2
                        linarith only [hlam, p1631_0]
              · linarith only [h1, h1532, h1622, hlam]
            · linarith only [h1, h1531, h1621, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1659 | h1659
      · linarith only [h0, h1, h1659, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1661 | h1661
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1662 | h1662
          · linarith only [h0, h1532, h1662, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1664 | h1664
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1665 | h1665
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1666 | h1666
                · linarith only [h0, h1532, h1661, h1666, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1668 | h1668
                  · linarith only [h1531, h1532, h1666, h1668, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h1531, h1532, h1668, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1671 | h1671
                · linarith only [h0, h1532, h1661, h1671, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1673 | h1673
                  · linarith only [h1531, h1671, h1673, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h1531, h1532, h1673, hc45, hlam, hphi, u4ehi1]
            · linarith only [h1, h1531, h1664, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1677 | h1677
          · linarith only [h0, h1532, h1677, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1679 | h1679
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1680 | h1680
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1681 | h1681
                · linarith only [h1531, h1532, h1681, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1683 | h1683
                  · linarith only [h1531, h1681, h1683, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h1531, h1532, h1683, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1686 | h1686
                · linarith only [h1531, h1532, h1686, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1688 | h1688
                  · linarith only [h1531, h1686, h1688, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h1531, h1532, h1688, hc45, hlam, hphi, u4ehi1]
            · linarith only [h1, h1531, h1679, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1692 | h1692
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1693 | h1693
      · linarith only [h0, h1, h1693, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1695 | h1695
        · linarith only [h0, h1531, h1695, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1697 | h1697
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1698 | h1698
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1699 | h1699
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1700 | h1700
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1701 | h1701
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1702 | h1702
                    · rcases h0bigk with h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1531, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1, hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1531, hlam, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1531, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h0, hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1693, hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1695, hlam, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h0, h1531, h1699, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1693, hc02, hc23, hlam, hphi, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1693, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1703_1, u4ehi0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1693, h1700, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1703_1, u4ehi4]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1695, h1697, h1700, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1703_1, u4ehi4]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1698, hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1693, h1698, h1700, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1703_1, u4ehi4]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1692, hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1697, hlam, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1699, hlam, p1703_0]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [h1700, hlam, p1703_1]
                      · have p1703_0 := h1703c.1
                        have p1703_1 := h1703c.2.1
                        have p1703_2 := h1703c.2.2.1
                        have p1703_3 := h1703c.2.2.2
                        linarith only [hlam, p1703_0]
                    · linarith only [h1, h1692, h1701, h1702, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1531, h1701, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h1531, h1697, h1700, hlam]
              · linarith only [h0, h1, h1697, h1699, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1733 | h1733
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1734 | h1734
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1735 | h1735
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1736 | h1736
                    · rcases h0bigk with h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1, h1698, hc02, hc34, hlam, hphi, ht23, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1, hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1531, hlam, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1, h1692, h1698, h1735, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1737_1, u4ehi4]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h0, hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1693, hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1695, hlam, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1692, h1735, hc02, hlam, hphi, ht0b, ht45, ht5b, p1737_1, u4ehi4]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1698, hc01, hc34, hlam, hphi, ht12, ht23, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1698, hc02, hc34, hlam, hphi, ht23, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1698, hlam, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1692, h1698, h1735, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1737_1, u4ehi4]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1692, h1695, h1697, h1735, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1737_1, u4ehi4]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1, h1692, h1698, h1735, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1737_1, u4ehi4]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1692, h1698, h1735, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1737_1, u4ehi4]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1692, hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1697, hlam, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1733, hlam, p1737_0]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [h1734, hlam, p1737_1]
                      · have p1737_0 := h1737c.1
                        have p1737_1 := h1737c.2.1
                        have p1737_2 := h1737c.2.2.1
                        have p1737_3 := h1737c.2.2.2
                        linarith only [hlam, p1737_0]
                    · linarith only [h1, h1692, h1698, h1735, h1736, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h0, h1531, h1735, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h1, h1697, h1698, h1734, hlam]
              · linarith only [h0, h1, h1697, h1733, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1767 | h1767
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1768 | h1768
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1769 | h1769
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1770 | h1770
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1771 | h1771
                    · rcases h0bigk with h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1531, hlam, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h0, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1693, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1695, hlam, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1697, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h0, h1693, hc12, hc23, hlam, hphi, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1531, h1692, h1693, h1770, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1772_1, u4ehi4]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1692, h1693, h1770, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1772_1, u4ehi4]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1692, h1770, hc04, hlam, hphi, ht0b, ht45, ht5b, p1772_1, u4ehi4]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h0, h1695, hc12, hc24, hlam, hphi, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1767, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1692, h1693, h1767, h1770, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1772_1, u4ehi4]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1692, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h0, h1, h1692, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1768, hlam, p1772_0]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [h1769, hlam, p1772_1]
                      · have p1772_0 := h1772c.1
                        have p1772_1 := h1772c.2.1
                        have p1772_2 := h1772c.2.2.1
                        have p1772_3 := h1772c.2.2.2
                        linarith only [hlam, p1772_0]
                    · linarith only [h1, h1692, h1770, h1771, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h1531, h1693, h1767, h1769, h1770, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h1531, h1692, h1769, hlam]
              · linarith only [h1, h1692, h1768, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1802 | h1802
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1803 | h1803
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1804 | h1804
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1805 | h1805
                    · rcases h0bigk with h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h0, h1531, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1, hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1531, hlam, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1531, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1806_1]
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
                        linarith only [h1693, hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1695, hlam, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1697, hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1692, h1767, hc04, hc15, hlam, hphi, ht0b, ht5b, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h0, h1767, hc12, hc34, hlam, hphi, ht23, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1767, hlam, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1692, h1767, h1804, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1806_1, u4ehi4]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1692, h1767, h1804, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1806_1, u4ehi4]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h0, h1767, hc12, hc34, hlam, hphi, ht23, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1767, hc03, hc34, hlam, hphi, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1692, h1767, h1804, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1806_1, u4ehi4]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1692, hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h0, h1, h1692, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1802, hlam, p1806_0]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [h1803, hlam, p1806_1]
                      · have p1806_0 := h1806c.1
                        have p1806_1 := h1806c.2.1
                        have p1806_2 := h1806c.2.2.1
                        have p1806_3 := h1806c.2.2.2
                        linarith only [hlam, p1806_0]
                    · linarith only [h1, h1692, h1767, h1804, h1805, hlam]
                  · linarith only [h0, h1531, h1804, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1531, h1692, h1803, hlam]
              · linarith only [h1, h1692, h1802, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1836 | h1836
      · linarith only [h0, h1, h1836, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1838 | h1838
        · linarith only [h0, h1531, h1838, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1840 | h1840
          · linarith only [h0, h1692, h1840, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1842 | h1842
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1843 | h1843
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1844 | h1844
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1845 | h1845
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1846 | h1846
                    · rcases h0bigk with h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c | h1847c
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1692, h1845, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1, hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1531, hlam, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1692, hlam, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1836, hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1838, hlam, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1840, hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1836, hc01, hc23, hlam, hphi, ht12, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, h1836, hc12, hc23, hlam, hphi, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1836, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1847_1, u4ehi0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, h1692, h1836, hc12, hc23, hlam, hphi, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, h1838, hc12, hc24, hlam, hphi, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1842, hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, h1692, h1836, h1842, hc12, hc23, hlam, hphi, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h0, h1840, hc12, hc25, hlam, hphi, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1843, hlam, p1847_0]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [h1844, hlam, p1847_1]
                      · have p1847_0 := h1847c.1
                        have p1847_1 := h1847c.2.1
                        have p1847_2 := h1847c.2.2.1
                        have p1847_3 := h1847c.2.2.2
                        linarith only [hlam, p1847_0]
                    · rcases h0bigk with h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c | h1873c
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1, h1836, h1842, h1844, h1846, hc12, hc13, hc23, hlam, hphi, ht01, ht0b, ht45, ht5b, p1873_1, u4ehi3]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1, hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1531, hlam, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1692, hlam, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1836, hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1838, hlam, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1840, hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1836, hc01, hc23, hlam, hphi, ht12, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1836, hc12, hc23, hlam, hphi, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1836, h1844, h1846, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1873_1, u4ehi3]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1692, h1836, hc12, hc23, hlam, hphi, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1838, hc12, hc24, hlam, hphi, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1842, hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1692, h1836, h1842, hc12, hc23, hlam, hphi, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1836, h1842, h1844, h1846, hc05, hc12, hc23, hlam, hphi, ht0b, ht45, ht5b, p1873_1, u4ehi3]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h0, h1840, hc12, hc25, hlam, hphi, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1843, hlam, p1873_0]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [h1844, hlam, p1873_1]
                      · have p1873_0 := h1873c.1
                        have p1873_1 := h1873c.2.1
                        have p1873_2 := h1873c.2.2.1
                        have p1873_3 := h1873c.2.2.2
                        linarith only [hlam, p1873_0]
                  · linarith only [h0, h1531, h1836, h1842, h1844, h1845, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1900 | h1900
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1901 | h1901
                    · linarith only [h0, h1531, h1844, h1901, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1531, h1844, h1900, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1531, hlam, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1692, hlam, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1836, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1838, hlam, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1840, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1836, hc01, hc23, hlam, hphi, ht12, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1836, hc12, hc23, hlam, hphi, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1836, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1903_1, u4ehi0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1692, h1836, hc12, hc23, hlam, hphi, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1838, hc12, hc24, hlam, hphi, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1842, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1844, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h0, h1840, hc12, hc25, hlam, hphi, p1903_1]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1843, hlam, p1903_0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [h1844, hc45, hlam, hphi, p1903_1, u4ehi0]
                      · have p1903_0 := h1903c.1
                        have p1903_1 := h1903c.2.1
                        have p1903_2 := h1903c.2.2.1
                        have p1903_3 := h1903c.2.2.2
                        linarith only [hlam, p1903_0]
                  · linarith only [h0, h1531, h1900, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1930 | h1930
                · linarith only [h1842, h1843, h1930, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1932 | h1932
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1933 | h1933
                    · linarith only [h1842, h1930, h1933, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h1842, h1843, h1932, h1933, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1531, h1932, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1937 | h1937
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1939 | h1939
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1940 | h1940
                    · rcases h0bigk with h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c | h1941c
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, h1, h1842, h1937, h1940, hc12, hc13, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p1941_1, u4ehi4]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1, hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1531, hlam, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1692, hlam, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1836, hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1838, hlam, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1840, hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1842, hc01, hc34, hlam, hphi, ht12, ht23, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, h1842, hc12, hc34, hlam, hphi, ht23, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1842, hlam, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1842, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, h1842, h1937, h1940, hc04, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p1941_1, u4ehi4]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, h1838, hc12, hc24, hlam, hphi, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1842, h1937, h1940, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1941_1, u4ehi4]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, h1692, h1842, hc12, hc34, hlam, hphi, ht23, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h0, h1840, hc12, hc25, hlam, hphi, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1937, hlam, p1941_0]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [h1938, hlam, p1941_1]
                      · have p1941_0 := h1941c.1
                        have p1941_1 := h1941c.2.1
                        have p1941_2 := h1941c.2.2.1
                        have p1941_3 := h1941c.2.2.2
                        linarith only [hlam, p1941_0]
                    · linarith only [h0, h1, h1842, h1940, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h1531, h1842, h1937, h1938, h1939, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1842, h1937, h1938, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1970 | h1970
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1971 | h1971
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1972 | h1972
                    · rcases h0bigk with h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c | h1973c
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1531, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1692, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1836, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1838, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1840, hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1937, hc01, hc35, hlam, hphi, ht12, ht23, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h1937, hc12, hc35, hlam, hphi, ht23, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1842, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1937, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h1838, hc12, hc24, hlam, hphi, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1842, hc03, hc34, hlam, hphi, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h1, h1842, h1937, hc12, hc34, hlam, hphi, ht23, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h1840, hc12, hc25, hlam, hphi, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h0, h1, h1937, hc12, hc35, hlam, hphi, ht23, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [h1970, hlam, p1973_1]
                      · have p1973_0 := h1973c.1
                        have p1973_1 := h1973c.2.1
                        have p1973_2 := h1973c.2.2.1
                        have p1973_3 := h1973c.2.2.2
                        linarith only [hlam, p1973_0]
                    · linarith only [h1842, h1970, h1972, hlam]
                  · linarith only [h0, h1531, h1842, h1970, h1971, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2001 | h2001
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2002 | h2002
                    · linarith only [h0, h1531, h1970, h2002, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1842, h2002, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h1531, h2001, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0 m hb0 hb2 hb4 h0 h1
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x1 m hb0 hb2 hb4 h0 h1

end R2N4
