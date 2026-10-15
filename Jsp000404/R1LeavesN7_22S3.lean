import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x9 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 2) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 2) ∧ (m.d 0 5) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 5) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h1599 | h1599
  · rcases p1573_3 (m.d 0 2) (by simp) with h1600 | h1600
    · rcases p1573_3 (m.d 0 3) (by simp) with h1601 | h1601
      · rcases p1573_3 (m.d 0 4) (by simp) with h1602 | h1602
        · rcases p1573_3 (m.d 0 5) (by simp) with h1603 | h1603
          · linarith only [h1557, h1603, hlam]
          · rcases h0emin with h1605 | h1605 | h1605 | h1605 | h1605
            · rcases h2bigk with h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c | h1606c
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1385, h1565, h1569, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1606_1]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h4, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1385, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                rcases p1606_3 (m.d 0 2) (by simp) with h1611 | h1611
                · rcases p1606_3 (m.d 1 2) (by simp) with h1612 | h1612
                  · linarith only [h0, h1612, hlam]
                  · linarith only [h1565, h1612, hlam]
                · linarith only [h1611, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h0, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1561, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1563, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                rcases p1606_3 (m.d 0 2) (by simp) with h1620 | h1620
                · rcases p1606_3 (m.d 1 2) (by simp) with h1621 | h1621
                  · rcases p1606_3 (m.d 2 3) (by simp) with h1622 | h1622
                    · rcases p1606_3 (m.d 2 4) (by simp) with h1623 | h1623
                      · rcases p1606_3 (m.d 2 5) (by simp) with h1624 | h1624
                        · linarith only [h1624, hlam, p1606_0]
                        · rcases h3bigk with h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1563, h1566, h1570, h1572, hc03, hc45, hlam, hphi, ht0b, ht5b, p1606_1, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h4, hlam, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            rcases p1626_3 (m.d 0 3) (by simp) with h1630 | h1630
                            · rcases p1626_3 (m.d 1 3) (by simp) with h1631 | h1631
                              · linarith only [h1, h1631, hlam]
                              · linarith only [h1566, h1631, hlam]
                            · linarith only [h1630, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            rcases p1626_3 (m.d 0 3) (by simp) with h1635 | h1635
                            · rcases p1626_3 (m.d 1 3) (by simp) with h1636 | h1636
                              · linarith only [h1, h1636, hlam]
                              · linarith only [h1567, h1636, hlam]
                            · linarith only [h1635, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1561, hlam, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            rcases p1626_3 (m.d 0 3) (by simp) with h1644 | h1644
                            · rcases p1626_3 (m.d 1 3) (by simp) with h1645 | h1645
                              · rcases p1626_3 (m.d 2 3) (by simp) with h1646 | h1646
                                · rcases p1626_3 (m.d 3 4) (by simp) with h1647 | h1647
                                  · linarith only [h1566, h1647, hlam]
                                  · linarith only [h1572, h1647, hlam]
                                · linarith only [h1570, h1646, hlam]
                              · linarith only [h1645, hlam, p1626_0]
                            · linarith only [h1559, h1644, hlam]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h0, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1606_1, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1561, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1606_1, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            rcases p1626_3 (m.d 0 3) (by simp) with h1656 | h1656
                            · linarith only [h1656, h4, hlam]
                            · linarith only [h1558, h1656, hlam]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1565, h1570, h3, h4, hlam, p1573_1, p1626_2]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1558, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1566, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1569, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1626_1]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1559, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1567, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1570, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [h1572, hlam, p1626_0]
                          · have p1626_0 := h1626c.1
                            have p1626_1 := h1626c.2.1
                            have p1626_2 := h1626c.2.2.1
                            have p1626_3 := h1626c.2.2.2
                            linarith only [hlam, p1626_0]
                      · linarith only [h1571, h1623, hlam]
                    · linarith only [h1570, h1622, hlam]
                  · linarith only [h1621, hlam, p1606_0]
                · linarith only [h1557, h1620, hlam]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1565, h1570, h1572, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1606_1]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                rcases p1606_3 (m.d 0 2) (by simp) with h1675 | h1675
                · linarith only [h1675, h4, hlam]
                · linarith only [h0, h1675, hlam]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1385, h1565, h1570, h1572, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1606_1]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1565, h3, h4, hlam, p1573_1, p1606_2]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1565, h1570, h1572, h3, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1606_1]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                rcases p1606_3 (m.d 0 2) (by simp) with h1682 | h1682
                · linarith only [h1385, h1682, hlam]
                · linarith only [h0, h1682, hlam]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1569, hlam, p1606_1]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1385, h1565, h3, hlam, p1573_1, p1606_2]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1557, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1565, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1570, hlam, p1606_1]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [h1571, hlam, p1606_0]
              · have p1606_0 := h1606c.1
                have p1606_1 := h1606c.2.1
                have p1606_2 := h1606c.2.2.1
                have p1606_3 := h1606c.2.2.2
                linarith only [hlam, p1606_0]
            · linarith only [h1385, h1569, h1605, hc23, hlam, ht01, ht12]
            · rcases h2bigk with h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1385, h1569, hc12, hc23, hlam, hphi, p1694_1]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h4, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1385, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                rcases p1694_3 (m.d 0 2) (by simp) with h1699 | h1699
                · rcases p1694_3 (m.d 1 2) (by simp) with h1700 | h1700
                  · linarith only [h0, h1700, hlam]
                  · linarith only [h1565, h1700, hlam]
                · linarith only [h1699, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h0, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1561, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1563, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                rcases p1694_3 (m.d 0 2) (by simp) with h1708 | h1708
                · rcases p1694_3 (m.d 1 2) (by simp) with h1709 | h1709
                  · rcases p1694_3 (m.d 2 3) (by simp) with h1710 | h1710
                    · rcases p1694_3 (m.d 2 4) (by simp) with h1711 | h1711
                      · rcases p1694_3 (m.d 2 5) (by simp) with h1712 | h1712
                        · linarith only [h1712, hlam, p1694_0]
                        · rcases h3bigk with h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1561, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1694_1, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h4, hlam, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            rcases p1714_3 (m.d 0 3) (by simp) with h1718 | h1718
                            · rcases p1714_3 (m.d 1 3) (by simp) with h1719 | h1719
                              · linarith only [h1, h1719, hlam]
                              · linarith only [h1566, h1719, hlam]
                            · linarith only [h1718, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            rcases p1714_3 (m.d 0 3) (by simp) with h1723 | h1723
                            · rcases p1714_3 (m.d 1 3) (by simp) with h1724 | h1724
                              · linarith only [h1, h1724, hlam]
                              · linarith only [h1567, h1724, hlam]
                            · linarith only [h1723, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1561, hlam, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            rcases p1714_3 (m.d 0 3) (by simp) with h1732 | h1732
                            · rcases p1714_3 (m.d 1 3) (by simp) with h1733 | h1733
                              · rcases p1714_3 (m.d 2 3) (by simp) with h1734 | h1734
                                · rcases p1714_3 (m.d 3 4) (by simp) with h1735 | h1735
                                  · linarith only [h1566, h1735, hlam]
                                  · linarith only [h1572, h1735, hlam]
                                · linarith only [h1570, h1734, hlam]
                              · linarith only [h1733, hlam, p1714_0]
                            · linarith only [h1559, h1732, hlam]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1605, hc23, hlam, ht01, ht12, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1561, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1694_1, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            rcases p1714_3 (m.d 0 3) (by simp) with h1744 | h1744
                            · linarith only [h1744, h4, hlam]
                            · linarith only [h1558, h1744, hlam]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h0, h1385, h1569, h1570, hlam, p1694_1, p1714_2]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1558, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1566, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1569, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1714_1]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1559, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1567, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1570, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [h1572, hlam, p1714_0]
                          · have p1714_0 := h1714c.1
                            have p1714_1 := h1714c.2.1
                            have p1714_2 := h1714c.2.2.1
                            have p1714_3 := h1714c.2.2.2
                            linarith only [hlam, p1714_0]
                      · linarith only [h1571, h1711, hlam]
                    · linarith only [h1570, h1710, hlam]
                  · linarith only [h1709, hlam, p1694_0]
                · linarith only [h1557, h1708, hlam]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1565, h1570, h1572, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1694_1]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                rcases p1694_3 (m.d 0 2) (by simp) with h1763 | h1763
                · linarith only [h1763, h4, hlam]
                · linarith only [h0, h1763, hlam]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1385, h1565, h1570, h1572, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1694_1]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1565, h3, h4, hlam, p1573_1, p1694_2]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1565, h1570, h1572, h3, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1694_1]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                rcases p1694_3 (m.d 0 2) (by simp) with h1770 | h1770
                · linarith only [h1385, h1770, hlam]
                · linarith only [h0, h1770, hlam]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1569, hlam, p1694_1]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1385, h1565, h3, hlam, p1573_1, p1694_2]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1557, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1565, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1570, hlam, p1694_1]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [h1571, hlam, p1694_0]
              · have p1694_0 := h1694c.1
                have p1694_1 := h1694c.2.1
                have p1694_2 := h1694c.2.2.1
                have p1694_3 := h1694c.2.2.2
                linarith only [hlam, p1694_0]
            · rcases h2bigk with h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c | h1781c
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1385, h1569, hc12, hc23, hlam, hphi, p1781_1]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h4, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1385, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                rcases p1781_3 (m.d 0 2) (by simp) with h1786 | h1786
                · rcases p1781_3 (m.d 1 2) (by simp) with h1787 | h1787
                  · linarith only [h0, h1787, hlam]
                  · linarith only [h1565, h1787, hlam]
                · linarith only [h1786, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h0, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1561, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1563, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                rcases p1781_3 (m.d 0 2) (by simp) with h1795 | h1795
                · rcases p1781_3 (m.d 1 2) (by simp) with h1796 | h1796
                  · rcases p1781_3 (m.d 2 3) (by simp) with h1797 | h1797
                    · rcases p1781_3 (m.d 2 4) (by simp) with h1798 | h1798
                      · rcases p1781_3 (m.d 2 5) (by simp) with h1799 | h1799
                        · linarith only [h1799, hlam, p1781_0]
                        · rcases h3bigk with h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c | h1801c
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1561, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1781_1, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h4, hlam, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            rcases p1801_3 (m.d 0 3) (by simp) with h1805 | h1805
                            · rcases p1801_3 (m.d 1 3) (by simp) with h1806 | h1806
                              · linarith only [h1, h1806, hlam]
                              · linarith only [h1566, h1806, hlam]
                            · linarith only [h1805, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            rcases p1801_3 (m.d 0 3) (by simp) with h1810 | h1810
                            · rcases p1801_3 (m.d 1 3) (by simp) with h1811 | h1811
                              · linarith only [h1, h1811, hlam]
                              · linarith only [h1567, h1811, hlam]
                            · linarith only [h1810, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1561, hlam, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            rcases p1801_3 (m.d 0 3) (by simp) with h1819 | h1819
                            · rcases p1801_3 (m.d 1 3) (by simp) with h1820 | h1820
                              · rcases p1801_3 (m.d 2 3) (by simp) with h1821 | h1821
                                · rcases p1801_3 (m.d 3 4) (by simp) with h1822 | h1822
                                  · linarith only [h1566, h1822, hlam]
                                  · linarith only [h1572, h1822, hlam]
                                · linarith only [h1570, h1821, hlam]
                              · linarith only [h1820, hlam, p1801_0]
                            · linarith only [h1559, h1819, hlam]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1565, h1570, h1572, h3, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1561, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1781_1, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            rcases p1801_3 (m.d 0 3) (by simp) with h1831 | h1831
                            · linarith only [h1831, h4, hlam]
                            · linarith only [h1558, h1831, hlam]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1565, h1570, h3, h4, hlam, p1573_1, p1801_2]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1558, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1566, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1569, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1801_1]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1559, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1567, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1570, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [h1572, hlam, p1801_0]
                          · have p1801_0 := h1801c.1
                            have p1801_1 := h1801c.2.1
                            have p1801_2 := h1801c.2.2.1
                            have p1801_3 := h1801c.2.2.2
                            linarith only [hlam, p1801_0]
                      · linarith only [h1571, h1798, hlam]
                    · linarith only [h1570, h1797, hlam]
                  · linarith only [h1796, hlam, p1781_0]
                · linarith only [h1557, h1795, hlam]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1565, h1570, h1572, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1781_1]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                rcases p1781_3 (m.d 0 2) (by simp) with h1850 | h1850
                · linarith only [h1850, h4, hlam]
                · linarith only [h0, h1850, hlam]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1385, h1565, h1570, h1572, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1781_1]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1565, h3, h4, hlam, p1573_1, p1781_2]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1565, h1570, h1572, h3, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1781_1]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                rcases p1781_3 (m.d 0 2) (by simp) with h1857 | h1857
                · linarith only [h1385, h1857, hlam]
                · linarith only [h0, h1857, hlam]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1569, hlam, p1781_1]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1385, h1565, h3, hlam, p1573_1, p1781_2]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1557, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1565, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1570, hlam, p1781_1]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [h1571, hlam, p1781_0]
              · have p1781_0 := h1781c.1
                have p1781_1 := h1781c.2.1
                have p1781_2 := h1781c.2.2.1
                have p1781_3 := h1781c.2.2.2
                linarith only [hlam, p1781_0]
            · linarith only [h1605, hc02, hlam, p1573_1]
        · linarith only [h1560, h1602, hlam]
      · linarith only [h1559, h1601, hlam]
    · linarith only [h1557, h1600, hlam]
  · linarith only [h1599, h3, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x10 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 3) ∧ (m.d 0 1) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 1) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1, hlam, p1573_1]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x11 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 3) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 3) ∧ (m.d 0 2) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 2) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h1874 | h1874
  · rcases p1573_3 (m.d 0 2) (by simp) with h1875 | h1875
    · linarith only [h1875, h4, hlam]
    · rcases p1573_3 (m.d 0 3) (by simp) with h1877 | h1877
      · rcases p1573_3 (m.d 0 4) (by simp) with h1878 | h1878
        · linarith only [h1558, h1878, hlam]
        · linarith only [h1385, h1878, hlam]
      · linarith only [h1877, h4, hlam]
  · linarith only [h0, h1874, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x12 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 3) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 3) ∧ (m.d 0 3) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 3) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x13 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 3) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 3) ∧ (m.d 0 4) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 4) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h1884 | h1884
  · rcases p1573_3 (m.d 0 2) (by simp) with h1885 | h1885
    · linarith only [h1885, h4, hlam]
    · rcases p1573_3 (m.d 0 3) (by simp) with h1887 | h1887
      · rcases p1573_3 (m.d 0 4) (by simp) with h1888 | h1888
        · linarith only [h1558, h1888, hlam]
        · rcases p1573_3 (m.d 0 5) (by simp) with h1890 | h1890
          · linarith only [h1559, h1890, hlam]
          · rcases h0emin with h1892 | h1892 | h1892 | h1892 | h1892
            · rcases h2bigk with h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1385, h4, hc12, hc23, hlam, hphi, p1573_1, p1893_1]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h4, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1385, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1385, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1893_1]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h0, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1561, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1563, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h0, h1385, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1893_1]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                rcases p1893_3 (m.d 0 2) (by simp) with h1904 | h1904
                · linarith only [h1904, hlam, p1893_0]
                · rcases p1893_3 (m.d 1 2) (by simp) with h1906 | h1906
                  · linarith only [h1561, h1906, hlam]
                  · rcases p1893_3 (m.d 2 3) (by simp) with h1908 | h1908
                    · rcases p1893_3 (m.d 2 4) (by simp) with h1909 | h1909
                      · linarith only [h1569, h1909, hlam]
                      · linarith only [h1385, h1909, hlam]
                    · linarith only [h1908, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                rcases p1893_3 (m.d 0 2) (by simp) with h1913 | h1913
                · linarith only [h1913, h4, hlam]
                · linarith only [h0, h1913, hlam]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1385, hc02, hc23, hlam, hphi, p1893_1]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h0, h1385, h1565, h4, hlam, p1573_1, p1893_2]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                rcases p1893_3 (m.d 0 2) (by simp) with h1919 | h1919
                · linarith only [h1919, hlam, p1893_0]
                · rcases p1893_3 (m.d 1 2) (by simp) with h1921 | h1921
                  · linarith only [h1563, h1921, hlam]
                  · rcases p1893_3 (m.d 2 3) (by simp) with h1923 | h1923
                    · rcases p1893_3 (m.d 2 4) (by simp) with h1924 | h1924
                      · rcases p1893_3 (m.d 2 5) (by simp) with h1925 | h1925
                        · linarith only [h1571, h1925, hlam]
                        · rcases h3bigk with h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c | h1927c
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1566, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h4, hlam, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            rcases p1927_3 (m.d 0 3) (by simp) with h1931 | h1931
                            · rcases p1927_3 (m.d 1 3) (by simp) with h1932 | h1932
                              · linarith only [h1, h1932, hlam]
                              · linarith only [h1566, h1932, hlam]
                            · linarith only [h1931, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h0, h1385, h1565, h1570, hlam, p1573_1, p1927_2]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1561, hlam, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            rcases p1927_3 (m.d 0 3) (by simp) with h1941 | h1941
                            · rcases p1927_3 (m.d 1 3) (by simp) with h1942 | h1942
                              · rcases p1927_3 (m.d 2 3) (by simp) with h1943 | h1943
                                · rcases p1927_3 (m.d 3 4) (by simp) with h1944 | h1944
                                  · linarith only [h1566, h1944, hlam]
                                  · linarith only [h1572, h1944, hlam]
                                · linarith only [h1570, h1943, hlam]
                              · linarith only [h1942, hlam, p1927_0]
                            · linarith only [h1559, h1941, hlam]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1385, hc02, hc23, hlam, hphi, p1573_1, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1566, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            rcases p1927_3 (m.d 0 3) (by simp) with h1953 | h1953
                            · linarith only [h1953, h4, hlam]
                            · linarith only [h1558, h1953, hlam]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h0, h1385, h1565, h1570, h4, hlam, p1573_1, p1927_2]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1558, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1566, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1569, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1927_1]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1559, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1567, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1570, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [h1572, hlam, p1927_0]
                          · have p1927_0 := h1927c.1
                            have p1927_1 := h1927c.2.1
                            have p1927_2 := h1927c.2.2.1
                            have p1927_3 := h1927c.2.2.2
                            linarith only [hlam, p1927_0]
                      · linarith only [h1924, hlam, p1893_0]
                    · linarith only [h1923, h4, hlam]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                rcases p1893_3 (m.d 0 2) (by simp) with h1969 | h1969
                · linarith only [h1385, h1969, hlam]
                · linarith only [h0, h1969, hlam]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1569, hlam, p1893_1]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                rcases p1893_3 (m.d 0 2) (by simp) with h1974 | h1974
                · linarith only [h1385, h1974, hlam]
                · linarith only [h1557, h1974, hlam]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1557, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1565, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1570, hlam, p1893_1]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [h1571, hlam, p1893_0]
              · have p1893_0 := h1893c.1
                have p1893_1 := h1893c.2.1
                have p1893_2 := h1893c.2.2.1
                have p1893_3 := h1893c.2.2.2
                linarith only [hlam, p1893_0]
            · linarith only [h1385, h1892, hc03, hlam, p1573_1]
            · rcases h2bigk with h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c | h1983c
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1385, h1565, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1983_1]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h4, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1385, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1385, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1983_1]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h0, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1561, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1563, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h0, h1385, h1570, h1572, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p1983_1]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                rcases p1983_3 (m.d 0 2) (by simp) with h1994 | h1994
                · linarith only [h1994, hlam, p1983_0]
                · rcases p1983_3 (m.d 1 2) (by simp) with h1996 | h1996
                  · linarith only [h1561, h1996, hlam]
                  · rcases p1983_3 (m.d 2 3) (by simp) with h1998 | h1998
                    · rcases p1983_3 (m.d 2 4) (by simp) with h1999 | h1999
                      · linarith only [h1569, h1999, hlam]
                      · linarith only [h1385, h1999, hlam]
                    · linarith only [h1998, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                rcases p1983_3 (m.d 0 2) (by simp) with h2003 | h2003
                · linarith only [h2003, h4, hlam]
                · linarith only [h0, h2003, hlam]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1385, hc02, hc23, hlam, hphi, p1983_1]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h0, h1385, h1565, h4, hlam, p1573_1, p1983_2]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                rcases p1983_3 (m.d 0 2) (by simp) with h2009 | h2009
                · linarith only [h2009, hlam, p1983_0]
                · rcases p1983_3 (m.d 1 2) (by simp) with h2011 | h2011
                  · linarith only [h1563, h2011, hlam]
                  · rcases p1983_3 (m.d 2 3) (by simp) with h2013 | h2013
                    · rcases p1983_3 (m.d 2 4) (by simp) with h2014 | h2014
                      · rcases p1983_3 (m.d 2 5) (by simp) with h2015 | h2015
                        · linarith only [h1571, h2015, hlam]
                        · rcases h3bigk with h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c | h2017c
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1566, h1572, hc03, hc45, hlam, hphi, ht0b, ht5b, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h4, hlam, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            rcases p2017_3 (m.d 0 3) (by simp) with h2021 | h2021
                            · rcases p2017_3 (m.d 1 3) (by simp) with h2022 | h2022
                              · linarith only [h1, h2022, hlam]
                              · linarith only [h1566, h2022, hlam]
                            · linarith only [h2021, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h0, h1385, h1565, h1570, hlam, p1573_1, p2017_2]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1561, hlam, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            rcases p2017_3 (m.d 0 3) (by simp) with h2031 | h2031
                            · rcases p2017_3 (m.d 1 3) (by simp) with h2032 | h2032
                              · rcases p2017_3 (m.d 2 3) (by simp) with h2033 | h2033
                                · rcases p2017_3 (m.d 3 4) (by simp) with h2034 | h2034
                                  · linarith only [h1566, h2034, hlam]
                                  · linarith only [h1572, h2034, hlam]
                                · linarith only [h1570, h2033, hlam]
                              · linarith only [h2032, hlam, p2017_0]
                            · linarith only [h1559, h2031, hlam]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h0, h1385, h1565, h1570, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1566, h1572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            rcases p2017_3 (m.d 0 3) (by simp) with h2043 | h2043
                            · linarith only [h2043, h4, hlam]
                            · linarith only [h1558, h2043, hlam]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h0, h1385, h1565, h1570, h4, hlam, p1573_1, p2017_2]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1558, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1566, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1569, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p2017_1]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1559, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1567, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1570, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [h1572, hlam, p2017_0]
                          · have p2017_0 := h2017c.1
                            have p2017_1 := h2017c.2.1
                            have p2017_2 := h2017c.2.2.1
                            have p2017_3 := h2017c.2.2.2
                            linarith only [hlam, p2017_0]
                      · linarith only [h2014, hlam, p1983_0]
                    · linarith only [h2013, h4, hlam]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                rcases p1983_3 (m.d 0 2) (by simp) with h2059 | h2059
                · linarith only [h1385, h2059, hlam]
                · linarith only [h0, h2059, hlam]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1569, hlam, p1983_1]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                rcases p1983_3 (m.d 0 2) (by simp) with h2064 | h2064
                · linarith only [h1385, h2064, hlam]
                · linarith only [h1557, h2064, hlam]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1557, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1565, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1570, hlam, p1983_1]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [h1571, hlam, p1983_0]
              · have p1983_0 := h1983c.1
                have p1983_1 := h1983c.2.1
                have p1983_2 := h1983c.2.2.1
                have p1983_3 := h1983c.2.2.2
                linarith only [hlam, p1983_0]
            · linarith only [h1892, hc03, hlam, p1573_1]
            · linarith only [h1892, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
      · linarith only [h1558, h1887, hlam]
  · linarith only [h1884, h2, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x14 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 3) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 3) ∧ (m.d 0 5) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 5) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h2076 | h2076
  · rcases p1573_3 (m.d 0 2) (by simp) with h2077 | h2077
    · linarith only [h2077, h4, hlam]
    · linarith only [h1557, h2077, hlam]
  · linarith only [h2076, h3, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x15 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 4) ∧ (m.d 0 1) - (m.d 0 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 4) ∨ (m.d 0 1) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h2, hlam, p1573_0]

end R2N4
