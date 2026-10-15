import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8217 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8219 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h8221 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases h0bigk with h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h0, hlam, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8580 | h8580
    · rcases p8577_3 (m.d 0 2) (by simp) with h8581 | h8581
      · rcases p8577_3 (m.d 0 3) (by simp) with h8582 | h8582
        · linarith only [h6310, h8582, hlam]
        · rcases p8577_3 (m.d 0 4) (by simp) with h8584 | h8584
          · linarith only [h6311, h8584, hlam]
          · linarith only [h6316, h8584, hlam]
      · linarith only [h6313, h8581, hlam]
    · linarith only [h6310, h8580, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8589 | h8589
    · rcases p8577_3 (m.d 0 2) (by simp) with h8590 | h8590
      · rcases p8577_3 (m.d 0 3) (by simp) with h8591 | h8591
        · linarith only [h6310, h8591, hlam]
        · rcases p8577_3 (m.d 0 4) (by simp) with h8593 | h8593
          · linarith only [h6311, h8593, hlam]
          · rcases p8577_3 (m.d 0 5) (by simp) with h8595 | h8595
            · linarith only [h6312, h8595, hlam]
            · linarith only [h7118, h8595, hlam]
      · linarith only [h6314, h8590, hlam]
    · linarith only [h6311, h8589, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8600 | h8600
    · rcases p8577_3 (m.d 0 2) (by simp) with h8601 | h8601
      · rcases p8577_3 (m.d 0 3) (by simp) with h8602 | h8602
        · linarith only [h6310, h8602, hlam]
        · rcases p8577_3 (m.d 0 4) (by simp) with h8604 | h8604
          · linarith only [h6311, h8604, hlam]
          · rcases p8577_3 (m.d 0 5) (by simp) with h8606 | h8606
            · linarith only [h6312, h8606, hlam]
            · rcases h0emin with h8608 | h8608 | h8608 | h8608 | h8608
              · rcases h1bigk with h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c | h8609c
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h0, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  rcases p8609_3 (m.d 0 1) (by simp) with h8612 | h8612
                  · rcases p8609_3 (m.d 1 2) (by simp) with h8613 | h8613
                    · rcases p8609_3 (m.d 1 3) (by simp) with h8614 | h8614
                      · linarith only [h8614, hlam, p8609_0]
                      · rcases p8609_3 (m.d 1 4) (by simp) with h8616 | h8616
                        · linarith only [h6311, h8616, hlam]
                        · linarith only [h8209, h8616, hlam]
                    · linarith only [h8206, h8613, hlam]
                  · linarith only [h8612, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  rcases p8609_3 (m.d 0 1) (by simp) with h8621 | h8621
                  · rcases p8609_3 (m.d 1 2) (by simp) with h8622 | h8622
                    · rcases p8609_3 (m.d 1 3) (by simp) with h8623 | h8623
                      · linarith only [h6310, h8623, hlam]
                      · rcases p8609_3 (m.d 1 4) (by simp) with h8625 | h8625
                        · linarith only [h8625, hlam, p8609_0]
                        · rcases p8609_3 (m.d 1 5) (by simp) with h8627 | h8627
                          · linarith only [h6312, h8627, hlam]
                          · linarith only [h8213, h8627, hlam]
                    · linarith only [h8207, h8622, hlam]
                  · linarith only [h8621, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  rcases p8609_3 (m.d 0 1) (by simp) with h8632 | h8632
                  · rcases p8609_3 (m.d 1 2) (by simp) with h8633 | h8633
                    · rcases p8609_3 (m.d 1 3) (by simp) with h8634 | h8634
                      · linarith only [h6310, h8634, hlam]
                      · rcases p8609_3 (m.d 1 4) (by simp) with h8636 | h8636
                        · linarith only [h6311, h8636, hlam]
                        · rcases p8609_3 (m.d 1 5) (by simp) with h8638 | h8638
                          · linarith only [h8638, hlam, p8609_0]
                          · rcases h3bigk with h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6316, h8221, hc23, hc45, hlam, hphi, ht34, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6316, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6900, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6310, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8209, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8211, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6313, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8206, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8215, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8217, hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8221, hc03, hc45, hlam, hphi, ht34, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8221, hc23, hc45, hlam, hphi, ht34, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [hlam, p8640_0]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h8221, hlam, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              rcases p8640_3 (m.d 0 3) (by simp) with h8661 | h8661
                              · linarith only [h8661, hlam, p8640_0]
                              · rcases p8640_3 (m.d 1 3) (by simp) with h8663 | h8663
                                · linarith only [h8211, h8663, hlam]
                                · rcases p8640_3 (m.d 2 3) (by simp) with h8665 | h8665
                                  · linarith only [h8217, h8665, hlam]
                                  · rcases p8640_3 (m.d 3 4) (by simp) with h8667 | h8667
                                    · linarith only [h8221, h8667, hlam]
                                    · linarith only [h6316, h8667, hlam]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              rcases p8640_3 (m.d 0 3) (by simp) with h8670 | h8670
                              · linarith only [h6900, h8670, hlam]
                              · linarith only [h6310, h8670, hlam]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              rcases p8640_3 (m.d 0 3) (by simp) with h8673 | h8673
                              · linarith only [h6900, h8673, hlam]
                              · linarith only [h6313, h8673, hlam]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [h6310, h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8640_1]
                            · have p8640_0 := h8640c.1
                              have p8640_1 := h8640c.2.1
                              have p8640_2 := h8640c.2.2.1
                              have p8640_3 := h8640c.2.2.2
                              linarith only [hlam, p8640_0]
                    · linarith only [h8208, h8633, hlam]
                  · linarith only [h8632, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8608, hc12, hlam, ht01, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h0, h6310, h6316, h7118, hlam, p8577_1, p8609_2]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h0, h6311, h7118, hlam, p8577_1, p8609_2]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h0, h6312, hlam, p8577_1, p8609_2]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h6310, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8206, hlam, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8209, hlam, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8211, hlam, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h6311, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8207, hlam, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h6311, h7118, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p8577_1, p8609_1, u0elo0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8213, hlam, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h6312, hlam, p8609_0]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h8208, hlam, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8577_1, p8609_1]
                · have p8609_0 := h8609c.1
                  have p8609_1 := h8609c.2.1
                  have p8609_2 := h8609c.2.2.1
                  have p8609_3 := h8609c.2.2.2
                  linarith only [hlam, p8609_0]
              · rcases h1bigk with h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c | h8700c
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h0, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  rcases p8700_3 (m.d 0 1) (by simp) with h8703 | h8703
                  · rcases p8700_3 (m.d 1 2) (by simp) with h8704 | h8704
                    · rcases p8700_3 (m.d 1 3) (by simp) with h8705 | h8705
                      · linarith only [h8705, hlam, p8700_0]
                      · rcases p8700_3 (m.d 1 4) (by simp) with h8707 | h8707
                        · linarith only [h6311, h8707, hlam]
                        · linarith only [h8209, h8707, hlam]
                    · linarith only [h8206, h8704, hlam]
                  · linarith only [h8703, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  rcases p8700_3 (m.d 0 1) (by simp) with h8712 | h8712
                  · rcases p8700_3 (m.d 1 2) (by simp) with h8713 | h8713
                    · rcases p8700_3 (m.d 1 3) (by simp) with h8714 | h8714
                      · linarith only [h6310, h8714, hlam]
                      · rcases p8700_3 (m.d 1 4) (by simp) with h8716 | h8716
                        · linarith only [h8716, hlam, p8700_0]
                        · rcases p8700_3 (m.d 1 5) (by simp) with h8718 | h8718
                          · linarith only [h6312, h8718, hlam]
                          · linarith only [h8213, h8718, hlam]
                    · linarith only [h8207, h8713, hlam]
                  · linarith only [h8712, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  rcases p8700_3 (m.d 0 1) (by simp) with h8723 | h8723
                  · rcases p8700_3 (m.d 1 2) (by simp) with h8724 | h8724
                    · rcases p8700_3 (m.d 1 3) (by simp) with h8725 | h8725
                      · linarith only [h6310, h8725, hlam]
                      · rcases p8700_3 (m.d 1 4) (by simp) with h8727 | h8727
                        · linarith only [h6311, h8727, hlam]
                        · rcases p8700_3 (m.d 1 5) (by simp) with h8729 | h8729
                          · linarith only [h8729, hlam, p8700_0]
                          · rcases h3bigk with h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h0, h6316, h7118, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h0, h6316, h7118, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h6316, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h6900, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h6310, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8209, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8211, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h6313, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8206, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8215, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8217, hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8221, hc03, hc45, hlam, hphi, ht34, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8221, hc23, hc45, hlam, hphi, ht34, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [hlam, p8731_0]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h8221, hlam, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              rcases p8731_3 (m.d 0 3) (by simp) with h8752 | h8752
                              · linarith only [h8752, hlam, p8731_0]
                              · rcases p8731_3 (m.d 1 3) (by simp) with h8754 | h8754
                                · linarith only [h8211, h8754, hlam]
                                · rcases p8731_3 (m.d 2 3) (by simp) with h8756 | h8756
                                  · linarith only [h8217, h8756, hlam]
                                  · rcases p8731_3 (m.d 3 4) (by simp) with h8758 | h8758
                                    · linarith only [h8221, h8758, hlam]
                                    · linarith only [h6316, h8758, hlam]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              rcases p8731_3 (m.d 0 3) (by simp) with h8761 | h8761
                              · linarith only [h6900, h8761, hlam]
                              · linarith only [h6310, h8761, hlam]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              rcases p8731_3 (m.d 0 3) (by simp) with h8764 | h8764
                              · linarith only [h6900, h8764, hlam]
                              · linarith only [h6313, h8764, hlam]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [h6310, h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8731_1]
                            · have p8731_0 := h8731c.1
                              have p8731_1 := h8731c.2.1
                              have p8731_2 := h8731c.2.2.1
                              have p8731_3 := h8731c.2.2.2
                              linarith only [hlam, p8731_0]
                    · linarith only [h8208, h8724, hlam]
                  · linarith only [h8723, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h7118, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8577_1, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h0, h6311, h7118, h8209, hlam, p8577_1, p8700_2]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h0, h6311, h7118, hlam, p8577_1, p8700_2]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h0, h6312, hlam, p8577_1, p8700_2]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h6310, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h8206, hlam, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h8209, hlam, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h8211, hlam, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h6311, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h8207, hlam, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h6311, h7118, h8206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8577_1, p8700_1, u0elo0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h8213, hlam, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h6312, hlam, p8700_0]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h8208, hlam, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8577_1, p8700_1]
                · have p8700_0 := h8700c.1
                  have p8700_1 := h8700c.2.1
                  have p8700_2 := h8700c.2.2.1
                  have p8700_3 := h8700c.2.2.2
                  linarith only [hlam, p8700_0]
              · linarith only [h0, h6316, h7118, h8608, hc12, hlam, ht01, p8577_1]
              · linarith only [h0, h7118, h8608, hc12, hlam, ht01, p8577_1]
              · linarith only [h0, h8608, hc12, hlam, ht01, p8577_1]
      · linarith only [h6315, h8601, hlam]
    · linarith only [h6312, h8600, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6310, h8206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8577_1, u0elo1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8798 | h8798
    · linarith only [h0, h8798, hlam]
    · linarith only [h6310, h8798, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8801 | h8801
    · linarith only [h0, h8801, hlam]
    · linarith only [h6311, h8801, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8804 | h8804
    · linarith only [h0, h8804, hlam]
    · linarith only [h6312, h8804, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6310, hlam, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6313, hlam, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6316, hlam, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6900, hlam, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6311, hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6314, hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6310, h7118, h8206, hc23, hc45, hlam, hphi, ht34, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h7118, hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6312, hlam, p8577_0]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [h6315, hlam, p8577_1]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8819 | h8819
    · rcases p8577_3 (m.d 0 2) (by simp) with h8820 | h8820
      · rcases p8577_3 (m.d 0 3) (by simp) with h8821 | h8821
        · linarith only [h6900, h8821, hlam]
        · rcases p8577_3 (m.d 0 4) (by simp) with h8823 | h8823
          · linarith only [h7118, h8823, hlam]
          · linarith only [h6316, h8823, hlam]
      · linarith only [h6313, h8820, hlam]
    · linarith only [h6310, h8819, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    rcases p8577_3 (m.d 0 1) (by simp) with h8828 | h8828
    · rcases p8577_3 (m.d 0 2) (by simp) with h8829 | h8829
      · rcases p8577_3 (m.d 0 3) (by simp) with h8830 | h8830
        · linarith only [h6900, h8830, hlam]
        · rcases p8577_3 (m.d 0 4) (by simp) with h8832 | h8832
          · linarith only [h7118, h8832, hlam]
          · rcases p8577_3 (m.d 0 5) (by simp) with h8834 | h8834
            · rcases h0emin with h8835 | h8835 | h8835 | h8835 | h8835
              · rcases h1bigk with h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h0, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  rcases p8836_3 (m.d 0 1) (by simp) with h8839 | h8839
                  · rcases p8836_3 (m.d 1 2) (by simp) with h8840 | h8840
                    · rcases p8836_3 (m.d 1 3) (by simp) with h8841 | h8841
                      · linarith only [h8841, hlam, p8836_0]
                      · rcases p8836_3 (m.d 1 4) (by simp) with h8843 | h8843
                        · linarith only [h6311, h8843, hlam]
                        · linarith only [h8209, h8843, hlam]
                    · linarith only [h8206, h8840, hlam]
                  · linarith only [h8839, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  rcases p8836_3 (m.d 0 1) (by simp) with h8848 | h8848
                  · rcases p8836_3 (m.d 1 2) (by simp) with h8849 | h8849
                    · rcases p8836_3 (m.d 1 3) (by simp) with h8850 | h8850
                      · linarith only [h6310, h8850, hlam]
                      · rcases p8836_3 (m.d 1 4) (by simp) with h8852 | h8852
                        · linarith only [h8852, hlam, p8836_0]
                        · rcases p8836_3 (m.d 1 5) (by simp) with h8854 | h8854
                          · linarith only [h6312, h8854, hlam]
                          · linarith only [h8213, h8854, hlam]
                    · linarith only [h8207, h8849, hlam]
                  · linarith only [h8848, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  rcases p8836_3 (m.d 0 1) (by simp) with h8859 | h8859
                  · rcases p8836_3 (m.d 1 2) (by simp) with h8860 | h8860
                    · rcases p8836_3 (m.d 1 3) (by simp) with h8861 | h8861
                      · linarith only [h6310, h8861, hlam]
                      · rcases p8836_3 (m.d 1 4) (by simp) with h8863 | h8863
                        · linarith only [h6311, h8863, hlam]
                        · rcases p8836_3 (m.d 1 5) (by simp) with h8865 | h8865
                          · linarith only [h8865, hlam, p8836_0]
                          · rcases h3bigk with h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c | h8867c
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6316, h8221, hc23, hc45, hlam, hphi, ht34, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6316, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6900, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6310, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6310, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8867_1, u0elo0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8209, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8211, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6313, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8206, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8215, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8217, hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8221, hc03, hc45, hlam, hphi, ht34, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8221, hc23, hc45, hlam, hphi, ht34, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [hlam, p8867_0]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h8221, hlam, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              rcases p8867_3 (m.d 0 3) (by simp) with h8888 | h8888
                              · linarith only [h8888, hlam, p8867_0]
                              · rcases p8867_3 (m.d 1 3) (by simp) with h8890 | h8890
                                · linarith only [h8211, h8890, hlam]
                                · rcases p8867_3 (m.d 2 3) (by simp) with h8892 | h8892
                                  · linarith only [h8217, h8892, hlam]
                                  · rcases p8867_3 (m.d 3 4) (by simp) with h8894 | h8894
                                    · linarith only [h8221, h8894, hlam]
                                    · linarith only [h6316, h8894, hlam]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              rcases p8867_3 (m.d 0 3) (by simp) with h8897 | h8897
                              · linarith only [h6900, h8897, hlam]
                              · linarith only [h6310, h8897, hlam]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              rcases p8867_3 (m.d 0 3) (by simp) with h8900 | h8900
                              · linarith only [h6900, h8900, hlam]
                              · linarith only [h6313, h8900, hlam]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [h6310, h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8867_1]
                            · have p8867_0 := h8867c.1
                              have p8867_1 := h8867c.2.1
                              have p8867_2 := h8867c.2.2.1
                              have p8867_3 := h8867c.2.2.2
                              linarith only [hlam, p8867_0]
                    · linarith only [h8208, h8860, hlam]
                  · linarith only [h8859, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8835, hc12, hlam, ht01, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h0, h6310, h6312, h6316, hlam, p8577_1, p8836_2]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h0, h6311, h6312, hlam, p8577_1, p8836_2]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  rcases p8836_3 (m.d 0 1) (by simp) with h8911 | h8911
                  · linarith only [h0, h8911, hlam]
                  · linarith only [h6312, h8911, hlam]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h6310, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8206, hlam, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8209, hlam, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8211, hlam, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h6311, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8207, hlam, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h6311, h6312, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p8577_1, p8836_1, u0elo0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8213, hlam, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h6312, hlam, p8836_0]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h8208, hlam, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8836_1]
                · have p8836_0 := h8836c.1
                  have p8836_1 := h8836c.2.1
                  have p8836_2 := h8836c.2.2.1
                  have p8836_3 := h8836c.2.2.2
                  linarith only [hlam, p8836_0]
              · rcases h1bigk with h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h0, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  rcases p8929_3 (m.d 0 1) (by simp) with h8932 | h8932
                  · rcases p8929_3 (m.d 1 2) (by simp) with h8933 | h8933
                    · rcases p8929_3 (m.d 1 3) (by simp) with h8934 | h8934
                      · linarith only [h8934, hlam, p8929_0]
                      · rcases p8929_3 (m.d 1 4) (by simp) with h8936 | h8936
                        · linarith only [h6311, h8936, hlam]
                        · linarith only [h8209, h8936, hlam]
                    · linarith only [h8206, h8933, hlam]
                  · linarith only [h8932, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  rcases p8929_3 (m.d 0 1) (by simp) with h8941 | h8941
                  · rcases p8929_3 (m.d 1 2) (by simp) with h8942 | h8942
                    · rcases p8929_3 (m.d 1 3) (by simp) with h8943 | h8943
                      · linarith only [h6310, h8943, hlam]
                      · rcases p8929_3 (m.d 1 4) (by simp) with h8945 | h8945
                        · linarith only [h8945, hlam, p8929_0]
                        · rcases p8929_3 (m.d 1 5) (by simp) with h8947 | h8947
                          · linarith only [h6312, h8947, hlam]
                          · linarith only [h8213, h8947, hlam]
                    · linarith only [h8207, h8942, hlam]
                  · linarith only [h8941, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  rcases p8929_3 (m.d 0 1) (by simp) with h8952 | h8952
                  · rcases p8929_3 (m.d 1 2) (by simp) with h8953 | h8953
                    · rcases p8929_3 (m.d 1 3) (by simp) with h8954 | h8954
                      · linarith only [h6310, h8954, hlam]
                      · rcases p8929_3 (m.d 1 4) (by simp) with h8956 | h8956
                        · linarith only [h6311, h8956, hlam]
                        · rcases p8929_3 (m.d 1 5) (by simp) with h8958 | h8958
                          · linarith only [h8958, hlam, p8929_0]
                          · rcases h3bigk with h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c | h8960c
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h0, h6312, h6316, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h0, h6312, h6316, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h6316, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h6900, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h6310, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8209, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8211, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h6313, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8206, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8215, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8217, hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8221, hc03, hc45, hlam, hphi, ht34, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8221, hc23, hc45, hlam, hphi, ht34, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [hlam, p8960_0]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h8221, hlam, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              rcases p8960_3 (m.d 0 3) (by simp) with h8981 | h8981
                              · linarith only [h8981, hlam, p8960_0]
                              · rcases p8960_3 (m.d 1 3) (by simp) with h8983 | h8983
                                · linarith only [h8211, h8983, hlam]
                                · rcases p8960_3 (m.d 2 3) (by simp) with h8985 | h8985
                                  · linarith only [h8217, h8985, hlam]
                                  · rcases p8960_3 (m.d 3 4) (by simp) with h8987 | h8987
                                    · linarith only [h8221, h8987, hlam]
                                    · linarith only [h6316, h8987, hlam]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              rcases p8960_3 (m.d 0 3) (by simp) with h8990 | h8990
                              · linarith only [h6900, h8990, hlam]
                              · linarith only [h6310, h8990, hlam]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              rcases p8960_3 (m.d 0 3) (by simp) with h8993 | h8993
                              · linarith only [h6900, h8993, hlam]
                              · linarith only [h6313, h8993, hlam]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [h6310, h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p8960_1]
                            · have p8960_0 := h8960c.1
                              have p8960_1 := h8960c.2.1
                              have p8960_2 := h8960c.2.2.1
                              have p8960_3 := h8960c.2.2.2
                              linarith only [hlam, p8960_0]
                    · linarith only [h8208, h8953, hlam]
                  · linarith only [h8952, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h6312, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8577_1, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h0, h6310, h6312, h6316, hlam, p8577_1, p8929_2]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h0, h6311, h6312, hlam, p8577_1, p8929_2]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  rcases p8929_3 (m.d 0 1) (by simp) with h9004 | h9004
                  · linarith only [h0, h9004, hlam]
                  · linarith only [h6312, h9004, hlam]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h6310, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h8206, hlam, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h8209, hlam, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h8211, hlam, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h6311, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h8207, hlam, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h6311, h6312, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p8577_1, p8929_1, u0elo0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h8213, hlam, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h6312, hlam, p8929_0]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h8208, hlam, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8929_1]
                · have p8929_0 := h8929c.1
                  have p8929_1 := h8929c.2.1
                  have p8929_2 := h8929c.2.2.1
                  have p8929_3 := h8929c.2.2.2
                  linarith only [hlam, p8929_0]
              · linarith only [h0, h6312, h6316, h8835, hc12, hlam, ht01, p8577_1]
              · linarith only [h0, h6312, h8835, hc12, hlam, ht01, p8577_1]
              · rcases h1bigk with h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c | h9024c
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h0, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  rcases p9024_3 (m.d 0 1) (by simp) with h9027 | h9027
                  · rcases p9024_3 (m.d 1 2) (by simp) with h9028 | h9028
                    · rcases p9024_3 (m.d 1 3) (by simp) with h9029 | h9029
                      · linarith only [h9029, hlam, p9024_0]
                      · rcases p9024_3 (m.d 1 4) (by simp) with h9031 | h9031
                        · linarith only [h6311, h9031, hlam]
                        · linarith only [h8209, h9031, hlam]
                    · linarith only [h8206, h9028, hlam]
                  · linarith only [h9027, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  rcases p9024_3 (m.d 0 1) (by simp) with h9036 | h9036
                  · rcases p9024_3 (m.d 1 2) (by simp) with h9037 | h9037
                    · rcases p9024_3 (m.d 1 3) (by simp) with h9038 | h9038
                      · linarith only [h6310, h9038, hlam]
                      · rcases p9024_3 (m.d 1 4) (by simp) with h9040 | h9040
                        · linarith only [h9040, hlam, p9024_0]
                        · rcases p9024_3 (m.d 1 5) (by simp) with h9042 | h9042
                          · linarith only [h6312, h9042, hlam]
                          · linarith only [h8213, h9042, hlam]
                    · linarith only [h8207, h9037, hlam]
                  · linarith only [h9036, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  rcases p9024_3 (m.d 0 1) (by simp) with h9047 | h9047
                  · rcases p9024_3 (m.d 1 2) (by simp) with h9048 | h9048
                    · rcases p9024_3 (m.d 1 3) (by simp) with h9049 | h9049
                      · linarith only [h6310, h9049, hlam]
                      · rcases p9024_3 (m.d 1 4) (by simp) with h9051 | h9051
                        · linarith only [h6311, h9051, hlam]
                        · rcases p9024_3 (m.d 1 5) (by simp) with h9053 | h9053
                          · linarith only [h9053, hlam, p9024_0]
                          · rcases h3bigk with h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c | h9055c
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h0, h6312, h6316, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h0, h6312, h6316, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8577_1, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h6316, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h6900, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h6310, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h0, h6310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8209, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8211, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h6313, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8206, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8215, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8217, hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8221, hc03, hc45, hlam, hphi, ht34, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8206, h8221, hc23, hc45, hlam, hphi, ht34, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8221, hc23, hc45, hlam, hphi, ht34, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [hlam, p9055_0]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h8221, hlam, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              rcases p9055_3 (m.d 0 3) (by simp) with h9076 | h9076
                              · linarith only [h9076, hlam, p9055_0]
                              · rcases p9055_3 (m.d 1 3) (by simp) with h9078 | h9078
                                · linarith only [h8211, h9078, hlam]
                                · rcases p9055_3 (m.d 2 3) (by simp) with h9080 | h9080
                                  · linarith only [h8217, h9080, hlam]
                                  · rcases p9055_3 (m.d 3 4) (by simp) with h9082 | h9082
                                    · linarith only [h8221, h9082, hlam]
                                    · linarith only [h6316, h9082, hlam]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              rcases p9055_3 (m.d 0 3) (by simp) with h9085 | h9085
                              · linarith only [h6900, h9085, hlam]
                              · linarith only [h6310, h9085, hlam]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              rcases p9055_3 (m.d 0 3) (by simp) with h9088 | h9088
                              · linarith only [h6900, h9088, hlam]
                              · linarith only [h6313, h9088, hlam]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [h6310, h6316, h8206, h8221, hc23, hc45, hlam, hphi, ht34, p9055_1]
                            · have p9055_0 := h9055c.1
                              have p9055_1 := h9055c.2.1
                              have p9055_2 := h9055c.2.2.1
                              have p9055_3 := h9055c.2.2.2
                              linarith only [hlam, p9055_0]
                    · linarith only [h8208, h9048, hlam]
                  · linarith only [h9047, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h6312, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8577_1, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h0, h6311, h6312, h8209, hlam, p8577_1, p9024_2]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h0, h6311, h6312, hlam, p8577_1, p9024_2]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  rcases p9024_3 (m.d 0 1) (by simp) with h9099 | h9099
                  · linarith only [h0, h9099, hlam]
                  · linarith only [h6312, h9099, hlam]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h6310, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h8206, hlam, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h8209, hlam, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h8211, hlam, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h6311, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h8207, hlam, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h6311, h6312, h8206, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8577_1, p9024_1, u0elo0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h8213, hlam, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h6312, hlam, p9024_0]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h8208, hlam, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h0, h6312, h8206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [h0, h6312, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9024_1]
                · have p9024_0 := h9024c.1
                  have p9024_1 := h9024c.2.1
                  have p9024_2 := h9024c.2.2.1
                  have p9024_3 := h9024c.2.2.2
                  linarith only [hlam, p9024_0]
            · linarith only [h7118, h8834, hlam]
      · linarith only [h6314, h8829, hlam]
    · linarith only [h6311, h8828, hlam]
  · have p8577_0 := h8577c.1
    have p8577_1 := h8577c.2.1
    have p8577_2 := h8577c.2.2.1
    have p8577_3 := h8577c.2.2.2
    linarith only [hlam, p8577_0]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8217 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8219 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 3 4 5 (by decide) (by decide) with h8221 | h8221
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215 h8217 h8219 h8221
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215 h8217 h8219 h8221

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8217 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 2 4 5 (by decide) (by decide) with h8219 | h8219
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215 h8217 h8219
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215 h8217 h8219

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8215 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 2 3 5 (by decide) (by decide) with h8217 | h8217
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215 h8217
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215 h8217

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h8213 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 2 3 4 (by decide) (by decide) with h8215 | h8215
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213 h8215

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8211 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 4 5 (by decide) (by decide) with h8213 | h8213
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211 h8213

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8209 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 3 5 (by decide) (by decide) with h8211 | h8211
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209 h8211

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 3 4 (by decide) (by decide) with h8209 | h8209
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208 h8209

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8208 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h0, h6315, h8208, hlam]

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 1 2 5 (by decide) (by decide) with h8208 | h8208
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg6311 hg6312 hg6313 hg6314 hg6315 h6316 h6900 h7118 h8206 h8207 h8208

set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h6900 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7118 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8206 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8207 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  linarith only [h0, h6314, h8207, hlam]

end R2N4
