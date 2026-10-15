import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9635 | h9635
  · rcases p9633_3 (m.d 1 2) (by simp) with h9636 | h9636
    · linarith only [h9636, hlam, p9633_0]
    · rcases p9633_3 (m.d 1 3) (by simp) with h9638 | h9638
      · linarith only [h1, h9638, hlam]
      · rcases p9633_3 (m.d 1 4) (by simp) with h9640 | h9640
        · linarith only [h2, h9640, hlam]
        · rcases p9633_3 (m.d 1 5) (by simp) with h9642 | h9642
          · linarith only [h3, h9642, hlam]
          · rcases h1emax with h9644 | h9644 | h9644 | h9644 | h9644
            · linarith only [h9644, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9633_1]
            · rcases h2bigk with h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c | h9646c
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                rcases p9646_3 (m.d 0 2) (by simp) with h9648 | h9648
                · rcases p9646_3 (m.d 1 2) (by simp) with h9649 | h9649
                  · linarith only [h0, h9649, hlam]
                  · rcases p9646_3 (m.d 2 3) (by simp) with h9651 | h9651
                    · linarith only [h4, h9651, hlam]
                    · rcases p9646_3 (m.d 2 4) (by simp) with h9653 | h9653
                      · linarith only [h5, h9653, hlam]
                      · rcases p9646_3 (m.d 2 5) (by simp) with h9655 | h9655
                        · linarith only [h6, h9655, hlam]
                        · rcases h4bigk with h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h2, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h2, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9271, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9623, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h5, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9269, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9625, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9629, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h7, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9631, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h7, h9271, hc13, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 4) (by simp) with h9679 | h9679
                            · linarith only [h9, h9679, hlam]
                            · linarith only [h2, h9679, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 4) (by simp) with h9682 | h9682
                            · linarith only [h9, h9682, hlam]
                            · linarith only [h5, h9682, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                · linarith only [h0, h9648, hlam]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                rcases p9646_3 (m.d 0 2) (by simp) with h9688 | h9688
                · rcases p9646_3 (m.d 1 2) (by simp) with h9689 | h9689
                  · linarith only [h0, h9689, hlam]
                  · linarith only [h9268, h9689, hlam]
                · linarith only [h9688, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                rcases p9646_3 (m.d 0 2) (by simp) with h9693 | h9693
                · rcases p9646_3 (m.d 1 2) (by simp) with h9694 | h9694
                  · linarith only [h0, h9694, hlam]
                  · linarith only [h9269, h9694, hlam]
                · linarith only [h9693, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                rcases p9646_3 (m.d 0 2) (by simp) with h9698 | h9698
                · rcases p9646_3 (m.d 1 2) (by simp) with h9699 | h9699
                  · linarith only [h0, h9699, hlam]
                  · linarith only [h9270, h9699, hlam]
                · linarith only [h9698, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h0, hlam, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9625, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9625, h9629, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h4, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9268, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9625, hlam, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9627, hlam, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h5, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9269, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9629, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h6, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9270, hlam, p9646_0]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p9633_1, p9646_1]
              · have p9646_0 := h9646c.1
                have p9646_1 := h9646c.2.1
                have p9646_2 := h9646c.2.2.1
                have p9646_3 := h9646c.2.2.2
                linarith only [hlam, p9646_0]
            · rcases h2bigk with h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c | h9723c
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                rcases p9723_3 (m.d 0 2) (by simp) with h9725 | h9725
                · rcases p9723_3 (m.d 1 2) (by simp) with h9726 | h9726
                  · linarith only [h0, h9726, hlam]
                  · rcases p9723_3 (m.d 2 3) (by simp) with h9728 | h9728
                    · linarith only [h4, h9728, hlam]
                    · rcases p9723_3 (m.d 2 4) (by simp) with h9730 | h9730
                      · linarith only [h5, h9730, hlam]
                      · rcases p9723_3 (m.d 2 5) (by simp) with h9732 | h9732
                        · linarith only [h6, h9732, hlam]
                        · rcases h4bigk with h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c | h9734c
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9, hc14, hc45, hlam, hphi, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h2, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h2, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9271, hlam, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9623, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h5, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9269, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9625, hlam, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9629, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h7, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9631, hlam, p9734_0]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            rcases p9734_3 (m.d 0 4) (by simp) with h9756 | h9756
                            · linarith only [h9, h9756, hlam]
                            · linarith only [h2, h9756, hlam]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            rcases p9734_3 (m.d 0 4) (by simp) with h9759 | h9759
                            · linarith only [h9, h9759, hlam]
                            · linarith only [h5, h9759, hlam]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9734_1]
                          · have p9734_0 := h9734c.1
                            have p9734_1 := h9734c.2.1
                            have p9734_2 := h9734c.2.2.1
                            have p9734_3 := h9734c.2.2.2
                            linarith only [hlam, p9734_0]
                · linarith only [h0, h9725, hlam]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                rcases p9723_3 (m.d 0 2) (by simp) with h9765 | h9765
                · rcases p9723_3 (m.d 1 2) (by simp) with h9766 | h9766
                  · linarith only [h0, h9766, hlam]
                  · linarith only [h9268, h9766, hlam]
                · linarith only [h9765, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                rcases p9723_3 (m.d 0 2) (by simp) with h9770 | h9770
                · rcases p9723_3 (m.d 1 2) (by simp) with h9771 | h9771
                  · linarith only [h0, h9771, hlam]
                  · linarith only [h9269, h9771, hlam]
                · linarith only [h9770, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                rcases p9723_3 (m.d 0 2) (by simp) with h9775 | h9775
                · rcases p9723_3 (m.d 1 2) (by simp) with h9776 | h9776
                  · linarith only [h0, h9776, hlam]
                  · linarith only [h9270, h9776, hlam]
                · linarith only [h9775, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h0, hlam, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9625, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9625, h9629, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h4, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9268, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9625, hlam, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9627, hlam, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h5, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9269, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9629, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h6, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9270, hlam, p9723_0]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p9633_1, p9723_1]
              · have p9723_0 := h9723c.1
                have p9723_1 := h9723c.2.1
                have p9723_2 := h9723c.2.2.1
                have p9723_3 := h9723c.2.2.2
                linarith only [hlam, p9723_0]
            · rcases h2bigk with h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c | h9800c
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                rcases p9800_3 (m.d 0 2) (by simp) with h9802 | h9802
                · rcases p9800_3 (m.d 1 2) (by simp) with h9803 | h9803
                  · linarith only [h0, h9803, hlam]
                  · rcases p9800_3 (m.d 2 3) (by simp) with h9805 | h9805
                    · linarith only [h4, h9805, hlam]
                    · rcases p9800_3 (m.d 2 4) (by simp) with h9807 | h9807
                      · linarith only [h5, h9807, hlam]
                      · rcases p9800_3 (m.d 2 5) (by simp) with h9809 | h9809
                        · linarith only [h6, h9809, hlam]
                        · rcases h4bigk with h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c | h9811c
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9, hc14, hc45, hlam, hphi, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h2, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h2, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9271, hlam, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9623, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h5, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9269, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9625, hlam, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9629, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h7, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9631, hlam, p9811_0]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            rcases p9811_3 (m.d 0 4) (by simp) with h9833 | h9833
                            · linarith only [h9, h9833, hlam]
                            · linarith only [h2, h9833, hlam]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            rcases p9811_3 (m.d 0 4) (by simp) with h9836 | h9836
                            · linarith only [h9, h9836, hlam]
                            · linarith only [h5, h9836, hlam]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9811_1]
                          · have p9811_0 := h9811c.1
                            have p9811_1 := h9811c.2.1
                            have p9811_2 := h9811c.2.2.1
                            have p9811_3 := h9811c.2.2.2
                            linarith only [hlam, p9811_0]
                · linarith only [h0, h9802, hlam]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                rcases p9800_3 (m.d 0 2) (by simp) with h9842 | h9842
                · rcases p9800_3 (m.d 1 2) (by simp) with h9843 | h9843
                  · linarith only [h0, h9843, hlam]
                  · linarith only [h9268, h9843, hlam]
                · linarith only [h9842, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                rcases p9800_3 (m.d 0 2) (by simp) with h9847 | h9847
                · rcases p9800_3 (m.d 1 2) (by simp) with h9848 | h9848
                  · linarith only [h0, h9848, hlam]
                  · linarith only [h9269, h9848, hlam]
                · linarith only [h9847, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                rcases p9800_3 (m.d 0 2) (by simp) with h9852 | h9852
                · rcases p9800_3 (m.d 1 2) (by simp) with h9853 | h9853
                  · linarith only [h0, h9853, hlam]
                  · linarith only [h9270, h9853, hlam]
                · linarith only [h9852, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h0, hlam, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9625, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9625, h9629, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h4, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9268, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9625, hlam, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9627, hlam, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h5, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9269, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9629, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h6, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9270, hlam, p9800_0]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p9633_1, p9800_1]
              · have p9800_0 := h9800c.1
                have p9800_1 := h9800c.2.1
                have p9800_2 := h9800c.2.2.1
                have p9800_3 := h9800c.2.2.2
                linarith only [hlam, p9800_0]
            · rcases h2bigk with h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c | h9877c
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                rcases p9877_3 (m.d 0 2) (by simp) with h9879 | h9879
                · rcases p9877_3 (m.d 1 2) (by simp) with h9880 | h9880
                  · linarith only [h0, h9880, hlam]
                  · rcases p9877_3 (m.d 2 3) (by simp) with h9882 | h9882
                    · linarith only [h4, h9882, hlam]
                    · rcases p9877_3 (m.d 2 4) (by simp) with h9884 | h9884
                      · linarith only [h5, h9884, hlam]
                      · rcases p9877_3 (m.d 2 5) (by simp) with h9886 | h9886
                        · linarith only [h6, h9886, hlam]
                        · rcases h4bigk with h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c | h9888c
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9, hc14, hc45, hlam, hphi, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h2, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h2, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9271, hlam, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9623, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h5, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9269, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9625, hlam, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9629, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h7, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9631, hlam, p9888_0]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            rcases p9888_3 (m.d 0 4) (by simp) with h9910 | h9910
                            · linarith only [h9, h9910, hlam]
                            · linarith only [h2, h9910, hlam]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            rcases p9888_3 (m.d 0 4) (by simp) with h9913 | h9913
                            · linarith only [h9, h9913, hlam]
                            · linarith only [h5, h9913, hlam]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p9888_1]
                          · have p9888_0 := h9888c.1
                            have p9888_1 := h9888c.2.1
                            have p9888_2 := h9888c.2.2.1
                            have p9888_3 := h9888c.2.2.2
                            linarith only [hlam, p9888_0]
                · linarith only [h0, h9879, hlam]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                rcases p9877_3 (m.d 0 2) (by simp) with h9919 | h9919
                · rcases p9877_3 (m.d 1 2) (by simp) with h9920 | h9920
                  · linarith only [h0, h9920, hlam]
                  · linarith only [h9268, h9920, hlam]
                · linarith only [h9919, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                rcases p9877_3 (m.d 0 2) (by simp) with h9924 | h9924
                · rcases p9877_3 (m.d 1 2) (by simp) with h9925 | h9925
                  · linarith only [h0, h9925, hlam]
                  · linarith only [h9269, h9925, hlam]
                · linarith only [h9924, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                rcases p9877_3 (m.d 0 2) (by simp) with h9929 | h9929
                · rcases p9877_3 (m.d 1 2) (by simp) with h9930 | h9930
                  · linarith only [h0, h9930, hlam]
                  · linarith only [h9270, h9930, hlam]
                · linarith only [h9929, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h0, hlam, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p9633_1, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p9633_1, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h4, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9268, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9625, hlam, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9627, hlam, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h5, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9269, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9629, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h6, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9270, hlam, p9877_0]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9633_1, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p9633_1, p9877_1]
              · have p9877_0 := h9877c.1
                have p9877_1 := h9877c.2.1
                have p9877_2 := h9877c.2.2.1
                have p9877_3 := h9877c.2.2.2
                linarith only [hlam, p9877_0]
  · linarith only [h9635, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9955 | h9955
  · rcases p9633_3 (m.d 1 2) (by simp) with h9956 | h9956
    · linarith only [h0, h9956, hlam]
    · linarith only [h9268, h9956, hlam]
  · linarith only [h9955, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9960 | h9960
  · rcases p9633_3 (m.d 1 2) (by simp) with h9961 | h9961
    · linarith only [h0, h9961, hlam]
    · linarith only [h9269, h9961, hlam]
  · linarith only [h9960, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9965 | h9965
  · rcases p9633_3 (m.d 1 2) (by simp) with h9966 | h9966
    · linarith only [h0, h9966, hlam]
    · linarith only [h9270, h9966, hlam]
  · linarith only [h9965, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h0, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9972 | h9972
  · rcases p9633_3 (m.d 1 2) (by simp) with h9973 | h9973
    · rcases p9633_3 (m.d 1 3) (by simp) with h9974 | h9974
      · linarith only [h9268, h9974, hlam]
      · rcases p9633_3 (m.d 1 4) (by simp) with h9976 | h9976
        · linarith only [h9269, h9976, hlam]
        · linarith only [h9271, h9976, hlam]
    · linarith only [h9268, h9973, hlam]
  · linarith only [h1, h9972, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9981 | h9981
  · rcases p9633_3 (m.d 1 2) (by simp) with h9982 | h9982
    · rcases p9633_3 (m.d 1 3) (by simp) with h9983 | h9983
      · linarith only [h9268, h9983, hlam]
      · rcases p9633_3 (m.d 1 4) (by simp) with h9985 | h9985
        · linarith only [h9269, h9985, hlam]
        · rcases p9633_3 (m.d 1 5) (by simp) with h9987 | h9987
          · linarith only [h9270, h9987, hlam]
          · linarith only [h9623, h9987, hlam]
    · linarith only [h9269, h9982, hlam]
  · linarith only [h2, h9981, hlam]

end R2N4
