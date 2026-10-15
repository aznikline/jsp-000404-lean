import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h34592 | h34592
  · linarith only [h34592, hlam, p34277_0]
  · rcases p34277_3 (m.d 1 2) (by simp) with h34594 | h34594
    · rcases p34277_3 (m.d 1 3) (by simp) with h34595 | h34595
      · linarith only [h34261, h34595, hlam]
      · rcases p34277_3 (m.d 1 4) (by simp) with h34597 | h34597
        · linarith only [h34262, h34597, hlam]
        · rcases p34277_3 (m.d 1 5) (by simp) with h34599 | h34599
          · linarith only [h34263, h34599, hlam]
          · rcases h1emax with h34601 | h34601 | h34601 | h34601 | h34601
            · rcases h2bigk with h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c | h34602c
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h0, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                rcases p34602_3 (m.d 0 2) (by simp) with h34605 | h34605
                · rcases p34602_3 (m.d 1 2) (by simp) with h34606 | h34606
                  · rcases p34602_3 (m.d 2 3) (by simp) with h34607 | h34607
                    · linarith only [h34607, hlam, p34602_0]
                    · rcases p34602_3 (m.d 2 4) (by simp) with h34609 | h34609
                      · linarith only [h33191, h34609, hlam]
                      · linarith only [h34270, h34609, hlam]
                  · linarith only [h34261, h34606, hlam]
                · linarith only [h34605, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                rcases p34602_3 (m.d 0 2) (by simp) with h34614 | h34614
                · rcases p34602_3 (m.d 1 2) (by simp) with h34615 | h34615
                  · rcases p34602_3 (m.d 2 3) (by simp) with h34616 | h34616
                    · linarith only [h33190, h34616, hlam]
                    · rcases p34602_3 (m.d 2 4) (by simp) with h34618 | h34618
                      · linarith only [h34618, hlam, p34602_0]
                      · rcases p34602_3 (m.d 2 5) (by simp) with h34620 | h34620
                        · linarith only [h33192, h34620, hlam]
                        · linarith only [h34274, h34620, hlam]
                  · linarith only [h34262, h34615, hlam]
                · linarith only [h34614, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                rcases p34602_3 (m.d 0 2) (by simp) with h34625 | h34625
                · rcases p34602_3 (m.d 1 2) (by simp) with h34626 | h34626
                  · rcases p34602_3 (m.d 2 3) (by simp) with h34627 | h34627
                    · linarith only [h33190, h34627, hlam]
                    · rcases p34602_3 (m.d 2 4) (by simp) with h34629 | h34629
                      · linarith only [h33191, h34629, hlam]
                      · rcases p34602_3 (m.d 2 5) (by simp) with h34631 | h34631
                        · linarith only [h34631, hlam, p34602_0]
                        · rcases h4bigk with h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c | h34633c
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33188, h34261, h34264, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33193, hlam, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33836, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33188, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34264, hlam, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34268, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33191, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34262, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34270, hlam, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34274, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            rcases p34633_3 (m.d 0 4) (by simp) with h34649 | h34649
                            · linarith only [h33193, h34649, hlam]
                            · rcases p34633_3 (m.d 1 4) (by simp) with h34651 | h34651
                              · linarith only [h34264, h34651, hlam]
                              · rcases p34633_3 (m.d 2 4) (by simp) with h34653 | h34653
                                · linarith only [h34270, h34653, hlam]
                                · rcases p34633_3 (m.d 3 4) (by simp) with h34655 | h34655
                                  · rcases p34633_3 (m.d 4 5) (by simp) with h34656 | h34656
                                    · linarith only [h34276, h34656, hlam]
                                    · linarith only [h33836, h34656, hlam]
                                  · linarith only [h33193, h34655, hlam]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            rcases p34633_3 (m.d 0 4) (by simp) with h34660 | h34660
                            · linarith only [h33193, h34660, hlam]
                            · linarith only [h33188, h34660, hlam]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            rcases p34633_3 (m.d 0 4) (by simp) with h34663 | h34663
                            · linarith only [h33193, h34663, hlam]
                            · linarith only [h33191, h34663, hlam]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc34, hlam, hphi, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34633_1]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [h34276, hlam, p34633_0]
                          · have p34633_0 := h34633c.1
                            have p34633_1 := h34633c.2.1
                            have p34633_2 := h34633c.2.2.1
                            have p34633_3 := h34633c.2.2.2
                            linarith only [hlam, p34633_0]
                  · linarith only [h34263, h34626, hlam]
                · linarith only [h34625, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                rcases p34602_3 (m.d 0 2) (by simp) with h34675 | h34675
                · linarith only [h0, h34675, hlam]
                · rcases p34602_3 (m.d 1 2) (by simp) with h34677 | h34677
                  · rcases p34602_3 (m.d 2 3) (by simp) with h34678 | h34678
                    · linarith only [h34261, h34678, hlam]
                    · rcases p34602_3 (m.d 2 4) (by simp) with h34680 | h34680
                      · linarith only [h34262, h34680, hlam]
                      · rcases p34602_3 (m.d 2 5) (by simp) with h34682 | h34682
                        · linarith only [h34263, h34682, hlam]
                        · rcases h4bigk with h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c | h34684c
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34602_1, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34602_1, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h33193, hlam, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h33836, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h33188, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34602_1, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34264, hlam, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34268, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h33191, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34262, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34270, hlam, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34274, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            rcases p34684_3 (m.d 0 4) (by simp) with h34700 | h34700
                            · linarith only [h33193, h34700, hlam]
                            · rcases p34684_3 (m.d 1 4) (by simp) with h34702 | h34702
                              · linarith only [h34264, h34702, hlam]
                              · rcases p34684_3 (m.d 2 4) (by simp) with h34704 | h34704
                                · linarith only [h34270, h34704, hlam]
                                · rcases p34684_3 (m.d 3 4) (by simp) with h34706 | h34706
                                  · rcases p34684_3 (m.d 4 5) (by simp) with h34707 | h34707
                                    · linarith only [h34276, h34707, hlam]
                                    · linarith only [h33836, h34707, hlam]
                                  · linarith only [h33193, h34706, hlam]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            rcases p34684_3 (m.d 0 4) (by simp) with h34711 | h34711
                            · linarith only [h33193, h34711, hlam]
                            · linarith only [h33188, h34711, hlam]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            rcases p34684_3 (m.d 0 4) (by simp) with h34714 | h34714
                            · linarith only [h33193, h34714, hlam]
                            · linarith only [h33191, h34714, hlam]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h33193, h34276, hc03, hc34, hlam, hphi, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34684_1]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [h34276, hlam, p34684_0]
                          · have p34684_0 := h34684c.1
                            have p34684_1 := h34684c.2.1
                            have p34684_2 := h34684c.2.2.1
                            have p34684_3 := h34684c.2.2.2
                            linarith only [hlam, p34684_0]
                  · linarith only [h0, h34677, hlam]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33189, h34262, h34268, h34270, hlam, p34277_1, p34602_2]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33189, h34262, h34268, hlam, p34277_1, p34602_2]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33189, h34263, hlam, p34277_1, p34602_2]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33190, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h34261, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h34270, hlam, p34602_1]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h34272, hlam, p34602_1]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33191, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h34262, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33189, h34262, h34268, h34601, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34602_1]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h34274, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33192, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h34263, hlam, p34602_0]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33189, h34263, h34601, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34602_1]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [h33189, h34263, h34601, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34602_1]
              · have p34602_0 := h34602c.1
                have p34602_1 := h34602c.2.1
                have p34602_2 := h34602c.2.2.1
                have p34602_3 := h34602c.2.2.2
                linarith only [hlam, p34602_0]
            · linarith only [h34601, hc01, hlam, p34277_1]
            · rcases h2bigk with h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c | h34745c
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h0, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                rcases p34745_3 (m.d 0 2) (by simp) with h34748 | h34748
                · rcases p34745_3 (m.d 1 2) (by simp) with h34749 | h34749
                  · rcases p34745_3 (m.d 2 3) (by simp) with h34750 | h34750
                    · linarith only [h34750, hlam, p34745_0]
                    · rcases p34745_3 (m.d 2 4) (by simp) with h34752 | h34752
                      · linarith only [h33191, h34752, hlam]
                      · linarith only [h34270, h34752, hlam]
                  · linarith only [h34261, h34749, hlam]
                · linarith only [h34748, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                rcases p34745_3 (m.d 0 2) (by simp) with h34757 | h34757
                · rcases p34745_3 (m.d 1 2) (by simp) with h34758 | h34758
                  · rcases p34745_3 (m.d 2 3) (by simp) with h34759 | h34759
                    · linarith only [h33190, h34759, hlam]
                    · rcases p34745_3 (m.d 2 4) (by simp) with h34761 | h34761
                      · linarith only [h34761, hlam, p34745_0]
                      · rcases p34745_3 (m.d 2 5) (by simp) with h34763 | h34763
                        · linarith only [h33192, h34763, hlam]
                        · linarith only [h34274, h34763, hlam]
                  · linarith only [h34262, h34758, hlam]
                · linarith only [h34757, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                rcases p34745_3 (m.d 0 2) (by simp) with h34768 | h34768
                · rcases p34745_3 (m.d 1 2) (by simp) with h34769 | h34769
                  · rcases p34745_3 (m.d 2 3) (by simp) with h34770 | h34770
                    · linarith only [h33190, h34770, hlam]
                    · rcases p34745_3 (m.d 2 4) (by simp) with h34772 | h34772
                      · linarith only [h33191, h34772, hlam]
                      · rcases p34745_3 (m.d 2 5) (by simp) with h34774 | h34774
                        · linarith only [h34774, hlam, p34745_0]
                        · rcases h4bigk with h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c | h34776c
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33836, h34262, h34270, h34276, hc23, hc35, hlam, hphi, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33193, hlam, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33836, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33188, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34264, hlam, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34268, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33191, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34262, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34270, hlam, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34274, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            rcases p34776_3 (m.d 0 4) (by simp) with h34792 | h34792
                            · linarith only [h33193, h34792, hlam]
                            · rcases p34776_3 (m.d 1 4) (by simp) with h34794 | h34794
                              · linarith only [h34264, h34794, hlam]
                              · rcases p34776_3 (m.d 2 4) (by simp) with h34796 | h34796
                                · linarith only [h34270, h34796, hlam]
                                · rcases p34776_3 (m.d 3 4) (by simp) with h34798 | h34798
                                  · rcases p34776_3 (m.d 4 5) (by simp) with h34799 | h34799
                                    · linarith only [h34276, h34799, hlam]
                                    · linarith only [h33836, h34799, hlam]
                                  · linarith only [h33193, h34798, hlam]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            rcases p34776_3 (m.d 0 4) (by simp) with h34803 | h34803
                            · linarith only [h33193, h34803, hlam]
                            · linarith only [h33188, h34803, hlam]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            rcases p34776_3 (m.d 0 4) (by simp) with h34806 | h34806
                            · linarith only [h33193, h34806, hlam]
                            · linarith only [h33191, h34806, hlam]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc34, hlam, hphi, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34776_1]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [h34276, hlam, p34776_0]
                          · have p34776_0 := h34776c.1
                            have p34776_1 := h34776c.2.1
                            have p34776_2 := h34776c.2.2.1
                            have p34776_3 := h34776c.2.2.2
                            linarith only [hlam, p34776_0]
                  · linarith only [h34263, h34769, hlam]
                · linarith only [h34768, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                rcases p34745_3 (m.d 0 2) (by simp) with h34818 | h34818
                · linarith only [h0, h34818, hlam]
                · rcases p34745_3 (m.d 1 2) (by simp) with h34820 | h34820
                  · rcases p34745_3 (m.d 2 3) (by simp) with h34821 | h34821
                    · linarith only [h34261, h34821, hlam]
                    · rcases p34745_3 (m.d 2 4) (by simp) with h34823 | h34823
                      · linarith only [h34262, h34823, hlam]
                      · rcases p34745_3 (m.d 2 5) (by simp) with h34825 | h34825
                        · linarith only [h34263, h34825, hlam]
                        · rcases h4bigk with h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c | h34827c
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34745_1, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34745_1, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h33193, hlam, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h33836, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h33188, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34745_1, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34264, hlam, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34268, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h33191, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34262, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34270, hlam, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34274, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            rcases p34827_3 (m.d 0 4) (by simp) with h34843 | h34843
                            · linarith only [h33193, h34843, hlam]
                            · rcases p34827_3 (m.d 1 4) (by simp) with h34845 | h34845
                              · linarith only [h34264, h34845, hlam]
                              · rcases p34827_3 (m.d 2 4) (by simp) with h34847 | h34847
                                · linarith only [h34270, h34847, hlam]
                                · rcases p34827_3 (m.d 3 4) (by simp) with h34849 | h34849
                                  · rcases p34827_3 (m.d 4 5) (by simp) with h34850 | h34850
                                    · linarith only [h34276, h34850, hlam]
                                    · linarith only [h33836, h34850, hlam]
                                  · linarith only [h33193, h34849, hlam]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            rcases p34827_3 (m.d 0 4) (by simp) with h34854 | h34854
                            · linarith only [h33193, h34854, hlam]
                            · linarith only [h33188, h34854, hlam]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            rcases p34827_3 (m.d 0 4) (by simp) with h34857 | h34857
                            · linarith only [h33193, h34857, hlam]
                            · linarith only [h33191, h34857, hlam]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h33193, h34276, hc03, hc34, hlam, hphi, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34827_1]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [h34276, hlam, p34827_0]
                          · have p34827_0 := h34827c.1
                            have p34827_1 := h34827c.2.1
                            have p34827_2 := h34827c.2.2.1
                            have p34827_3 := h34827c.2.2.2
                            linarith only [hlam, p34827_0]
                  · linarith only [h0, h34820, hlam]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33189, h34262, h34268, h34270, hlam, p34277_1, p34745_2]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33189, h34262, h34268, hlam, p34277_1, p34745_2]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33189, h34263, hlam, p34277_1, p34745_2]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33190, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h34261, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h34270, hlam, p34745_1]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h34272, hlam, p34745_1]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33191, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h34262, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33189, h34262, h34268, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34745_1]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h34274, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33192, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h34263, hlam, p34745_0]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33189, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34745_1]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [h33189, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p34745_1]
              · have p34745_0 := h34745c.1
                have p34745_1 := h34745c.2.1
                have p34745_2 := h34745c.2.2.1
                have p34745_3 := h34745c.2.2.2
                linarith only [hlam, p34745_0]
            · rcases h2bigk with h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c | h34887c
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h0, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                rcases p34887_3 (m.d 0 2) (by simp) with h34890 | h34890
                · rcases p34887_3 (m.d 1 2) (by simp) with h34891 | h34891
                  · rcases p34887_3 (m.d 2 3) (by simp) with h34892 | h34892
                    · linarith only [h34892, hlam, p34887_0]
                    · rcases p34887_3 (m.d 2 4) (by simp) with h34894 | h34894
                      · linarith only [h33191, h34894, hlam]
                      · linarith only [h34270, h34894, hlam]
                  · linarith only [h34261, h34891, hlam]
                · linarith only [h34890, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                rcases p34887_3 (m.d 0 2) (by simp) with h34899 | h34899
                · rcases p34887_3 (m.d 1 2) (by simp) with h34900 | h34900
                  · rcases p34887_3 (m.d 2 3) (by simp) with h34901 | h34901
                    · linarith only [h33190, h34901, hlam]
                    · rcases p34887_3 (m.d 2 4) (by simp) with h34903 | h34903
                      · linarith only [h34903, hlam, p34887_0]
                      · rcases p34887_3 (m.d 2 5) (by simp) with h34905 | h34905
                        · linarith only [h33192, h34905, hlam]
                        · linarith only [h34274, h34905, hlam]
                  · linarith only [h34262, h34900, hlam]
                · linarith only [h34899, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                rcases p34887_3 (m.d 0 2) (by simp) with h34910 | h34910
                · rcases p34887_3 (m.d 1 2) (by simp) with h34911 | h34911
                  · rcases p34887_3 (m.d 2 3) (by simp) with h34912 | h34912
                    · linarith only [h33190, h34912, hlam]
                    · rcases p34887_3 (m.d 2 4) (by simp) with h34914 | h34914
                      · linarith only [h33191, h34914, hlam]
                      · rcases p34887_3 (m.d 2 5) (by simp) with h34916 | h34916
                        · linarith only [h34916, hlam, p34887_0]
                        · rcases h4bigk with h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c | h34918c
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33188, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33193, hlam, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33836, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33188, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34264, hlam, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34268, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33191, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34262, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34270, hlam, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34274, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            rcases p34918_3 (m.d 0 4) (by simp) with h34934 | h34934
                            · linarith only [h33193, h34934, hlam]
                            · rcases p34918_3 (m.d 1 4) (by simp) with h34936 | h34936
                              · linarith only [h34264, h34936, hlam]
                              · rcases p34918_3 (m.d 2 4) (by simp) with h34938 | h34938
                                · linarith only [h34270, h34938, hlam]
                                · rcases p34918_3 (m.d 3 4) (by simp) with h34940 | h34940
                                  · rcases p34918_3 (m.d 4 5) (by simp) with h34941 | h34941
                                    · linarith only [h34276, h34941, hlam]
                                    · linarith only [h33836, h34941, hlam]
                                  · linarith only [h33193, h34940, hlam]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            rcases p34918_3 (m.d 0 4) (by simp) with h34945 | h34945
                            · linarith only [h33193, h34945, hlam]
                            · linarith only [h33188, h34945, hlam]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            rcases p34918_3 (m.d 0 4) (by simp) with h34948 | h34948
                            · linarith only [h33193, h34948, hlam]
                            · linarith only [h33191, h34948, hlam]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc34, hlam, hphi, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34918_1]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [h34276, hlam, p34918_0]
                          · have p34918_0 := h34918c.1
                            have p34918_1 := h34918c.2.1
                            have p34918_2 := h34918c.2.2.1
                            have p34918_3 := h34918c.2.2.2
                            linarith only [hlam, p34918_0]
                  · linarith only [h34263, h34911, hlam]
                · linarith only [h34910, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                rcases p34887_3 (m.d 0 2) (by simp) with h34960 | h34960
                · linarith only [h0, h34960, hlam]
                · rcases p34887_3 (m.d 1 2) (by simp) with h34962 | h34962
                  · rcases p34887_3 (m.d 2 3) (by simp) with h34963 | h34963
                    · linarith only [h34261, h34963, hlam]
                    · rcases p34887_3 (m.d 2 4) (by simp) with h34965 | h34965
                      · linarith only [h34262, h34965, hlam]
                      · rcases p34887_3 (m.d 2 5) (by simp) with h34967 | h34967
                        · linarith only [h34263, h34967, hlam]
                        · rcases h4bigk with h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c | h34969c
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34887_1, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34887_1, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h33193, hlam, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h33836, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h33188, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34887_1, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34264, hlam, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34268, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h33191, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34262, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34270, hlam, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34274, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            rcases p34969_3 (m.d 0 4) (by simp) with h34985 | h34985
                            · linarith only [h33193, h34985, hlam]
                            · rcases p34969_3 (m.d 1 4) (by simp) with h34987 | h34987
                              · linarith only [h34264, h34987, hlam]
                              · rcases p34969_3 (m.d 2 4) (by simp) with h34989 | h34989
                                · linarith only [h34270, h34989, hlam]
                                · rcases p34969_3 (m.d 3 4) (by simp) with h34991 | h34991
                                  · rcases p34969_3 (m.d 4 5) (by simp) with h34992 | h34992
                                    · linarith only [h34276, h34992, hlam]
                                    · linarith only [h33836, h34992, hlam]
                                  · linarith only [h33193, h34991, hlam]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            rcases p34969_3 (m.d 0 4) (by simp) with h34996 | h34996
                            · linarith only [h33193, h34996, hlam]
                            · linarith only [h33188, h34996, hlam]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            rcases p34969_3 (m.d 0 4) (by simp) with h34999 | h34999
                            · linarith only [h33193, h34999, hlam]
                            · linarith only [h33191, h34999, hlam]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h33193, h34276, hc03, hc34, hlam, hphi, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p34969_1]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [h34276, hlam, p34969_0]
                          · have p34969_0 := h34969c.1
                            have p34969_1 := h34969c.2.1
                            have p34969_2 := h34969c.2.2.1
                            have p34969_3 := h34969c.2.2.2
                            linarith only [hlam, p34969_0]
                  · linarith only [h0, h34962, hlam]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33189, h34262, h34268, h34270, hlam, p34277_1, p34887_2]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33189, h34262, h34268, hlam, p34277_1, p34887_2]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33189, h34263, hlam, p34277_1, p34887_2]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33190, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h34261, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h34270, hlam, p34887_1]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h34272, hlam, p34887_1]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33191, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h34262, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33189, h34262, h34268, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34887_1]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h34274, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33192, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h34263, hlam, p34887_0]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33189, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p34887_1]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [h33189, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p34887_1]
              · have p34887_0 := h34887c.1
                have p34887_1 := h34887c.2.1
                have p34887_2 := h34887c.2.2.1
                have p34887_3 := h34887c.2.2.2
                linarith only [hlam, p34887_0]
            · rcases h2bigk with h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c | h35029c
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h0, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                rcases p35029_3 (m.d 0 2) (by simp) with h35032 | h35032
                · rcases p35029_3 (m.d 1 2) (by simp) with h35033 | h35033
                  · rcases p35029_3 (m.d 2 3) (by simp) with h35034 | h35034
                    · linarith only [h35034, hlam, p35029_0]
                    · rcases p35029_3 (m.d 2 4) (by simp) with h35036 | h35036
                      · linarith only [h33191, h35036, hlam]
                      · linarith only [h34270, h35036, hlam]
                  · linarith only [h34261, h35033, hlam]
                · linarith only [h35032, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                rcases p35029_3 (m.d 0 2) (by simp) with h35041 | h35041
                · rcases p35029_3 (m.d 1 2) (by simp) with h35042 | h35042
                  · rcases p35029_3 (m.d 2 3) (by simp) with h35043 | h35043
                    · linarith only [h33190, h35043, hlam]
                    · rcases p35029_3 (m.d 2 4) (by simp) with h35045 | h35045
                      · linarith only [h35045, hlam, p35029_0]
                      · rcases p35029_3 (m.d 2 5) (by simp) with h35047 | h35047
                        · linarith only [h33192, h35047, hlam]
                        · linarith only [h34274, h35047, hlam]
                  · linarith only [h34262, h35042, hlam]
                · linarith only [h35041, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                rcases p35029_3 (m.d 0 2) (by simp) with h35052 | h35052
                · rcases p35029_3 (m.d 1 2) (by simp) with h35053 | h35053
                  · rcases p35029_3 (m.d 2 3) (by simp) with h35054 | h35054
                    · linarith only [h33190, h35054, hlam]
                    · rcases p35029_3 (m.d 2 4) (by simp) with h35056 | h35056
                      · linarith only [h33191, h35056, hlam]
                      · rcases p35029_3 (m.d 2 5) (by simp) with h35058 | h35058
                        · linarith only [h35058, hlam, p35029_0]
                        · rcases h4bigk with h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c | h35060c
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33188, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33193, hlam, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33836, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33188, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34264, hlam, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34268, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33191, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34262, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34270, hlam, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34274, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            rcases p35060_3 (m.d 0 4) (by simp) with h35076 | h35076
                            · linarith only [h33193, h35076, hlam]
                            · rcases p35060_3 (m.d 1 4) (by simp) with h35078 | h35078
                              · linarith only [h34264, h35078, hlam]
                              · rcases p35060_3 (m.d 2 4) (by simp) with h35080 | h35080
                                · linarith only [h34270, h35080, hlam]
                                · rcases p35060_3 (m.d 3 4) (by simp) with h35082 | h35082
                                  · rcases p35060_3 (m.d 4 5) (by simp) with h35083 | h35083
                                    · linarith only [h34276, h35083, hlam]
                                    · linarith only [h33836, h35083, hlam]
                                  · linarith only [h33193, h35082, hlam]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            rcases p35060_3 (m.d 0 4) (by simp) with h35087 | h35087
                            · linarith only [h33193, h35087, hlam]
                            · linarith only [h33188, h35087, hlam]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            rcases p35060_3 (m.d 0 4) (by simp) with h35090 | h35090
                            · linarith only [h33193, h35090, hlam]
                            · linarith only [h33191, h35090, hlam]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc34, hlam, hphi, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p35060_1]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [h34276, hlam, p35060_0]
                          · have p35060_0 := h35060c.1
                            have p35060_1 := h35060c.2.1
                            have p35060_2 := h35060c.2.2.1
                            have p35060_3 := h35060c.2.2.2
                            linarith only [hlam, p35060_0]
                  · linarith only [h34263, h35053, hlam]
                · linarith only [h35052, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                rcases p35029_3 (m.d 0 2) (by simp) with h35102 | h35102
                · linarith only [h0, h35102, hlam]
                · rcases p35029_3 (m.d 1 2) (by simp) with h35104 | h35104
                  · rcases p35029_3 (m.d 2 3) (by simp) with h35105 | h35105
                    · linarith only [h34261, h35105, hlam]
                    · rcases p35029_3 (m.d 2 4) (by simp) with h35107 | h35107
                      · linarith only [h34262, h35107, hlam]
                      · rcases p35029_3 (m.d 2 5) (by simp) with h35109 | h35109
                        · linarith only [h34263, h35109, hlam]
                        · rcases h4bigk with h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c | h35111c
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35029_1, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35029_1, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h33193, hlam, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h33836, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h33188, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35029_1, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34264, hlam, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34268, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h33191, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34262, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34270, hlam, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34274, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            rcases p35111_3 (m.d 0 4) (by simp) with h35127 | h35127
                            · linarith only [h33193, h35127, hlam]
                            · rcases p35111_3 (m.d 1 4) (by simp) with h35129 | h35129
                              · linarith only [h34264, h35129, hlam]
                              · rcases p35111_3 (m.d 2 4) (by simp) with h35131 | h35131
                                · linarith only [h34270, h35131, hlam]
                                · rcases p35111_3 (m.d 3 4) (by simp) with h35133 | h35133
                                  · rcases p35111_3 (m.d 4 5) (by simp) with h35134 | h35134
                                    · linarith only [h34276, h35134, hlam]
                                    · linarith only [h33836, h35134, hlam]
                                  · linarith only [h33193, h35133, hlam]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            rcases p35111_3 (m.d 0 4) (by simp) with h35138 | h35138
                            · linarith only [h33193, h35138, hlam]
                            · linarith only [h33188, h35138, hlam]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            rcases p35111_3 (m.d 0 4) (by simp) with h35141 | h35141
                            · linarith only [h33193, h35141, hlam]
                            · linarith only [h33191, h35141, hlam]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h33191, h33836, h34270, hc23, hc34, hlam, hphi, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h33193, h34276, hc03, hc34, hlam, hphi, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc34, hlam, hphi, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34270, h34276, hc23, hc34, hlam, hphi, p35111_1]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [h34276, hlam, p35111_0]
                          · have p35111_0 := h35111c.1
                            have p35111_1 := h35111c.2.1
                            have p35111_2 := h35111c.2.2.1
                            have p35111_3 := h35111c.2.2.2
                            linarith only [hlam, p35111_0]
                  · linarith only [h0, h35104, hlam]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33189, h34262, h34268, h34270, hlam, p34277_1, p35029_2]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33189, h34262, h34268, hlam, p34277_1, p35029_2]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33189, h34263, hlam, p34277_1, p35029_2]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33190, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h34261, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h34270, hlam, p35029_1]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h34272, hlam, p35029_1]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33191, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h34262, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33189, h34262, h34268, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p35029_1]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h34274, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33192, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h34263, hlam, p35029_0]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33189, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p34277_1, p35029_1]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [h33189, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p34277_1, p35029_1]
              · have p35029_0 := h35029c.1
                have p35029_1 := h35029c.2.1
                have p35029_2 := h35029c.2.2.1
                have p35029_3 := h35029c.2.2.2
                linarith only [hlam, p35029_0]
    · linarith only [h34594, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h35173 | h35173
  · linarith only [h0, h35173, hlam]
  · linarith only [h33187, h35173, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h35176 | h35176
  · linarith only [h0, h35176, hlam]
  · linarith only [h33188, h35176, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  rcases p34277_3 (m.d 0 1) (by simp) with h35179 | h35179
  · linarith only [h0, h35179, hlam]
  · linarith only [h33189, h35179, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h33187, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h34261, hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [hlam, p34277_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h34277c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p34277_0 := h34277c.1
  have p34277_1 := h34277c.2.1
  have p34277_2 := h34277c.2.2.1
  have p34277_3 := h34277c.2.2.2
  linarith only [h34264, hlam, p34277_0]

end R2N4
