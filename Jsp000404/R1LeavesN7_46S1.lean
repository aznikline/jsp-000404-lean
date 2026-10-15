import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h568 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h569 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h570 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
  · rcases h0bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h0, hlam, p572_1]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h451, hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h451, h558, h561, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u2ehi4]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h0, h558, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u2ehi4]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h578 | h578
      · linarith only [h0, h578, hlam]
      · rcases p572_3 (m.d 0 2) (by simp) with h580 | h580
        · rcases p572_3 (m.d 0 3) (by simp) with h581 | h581
          · linarith only [h556, h581, hlam]
          · linarith only [h451, h581, hlam]
        · linarith only [h0, h580, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h556, h568, h571, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u3ehi4]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h587 | h587
      · linarith only [h0, h587, hlam]
      · rcases p572_3 (m.d 0 2) (by simp) with h589 | h589
        · rcases p572_3 (m.d 0 3) (by simp) with h590 | h590
          · linarith only [h556, h590, hlam]
          · linarith only [h559, h590, hlam]
        · linarith only [h557, h589, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h594 | h594
      · linarith only [h0, h594, hlam]
      · rcases p572_3 (m.d 0 2) (by simp) with h596 | h596
        · rcases p572_3 (m.d 0 3) (by simp) with h597 | h597
          · linarith only [h556, h597, hlam]
          · linarith only [h560, h597, hlam]
        · linarith only [h558, h596, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h601 | h601
      · linarith only [h451, h601, hlam]
      · rcases p572_3 (m.d 0 2) (by simp) with h603 | h603
        · rcases p572_3 (m.d 0 3) (by simp) with h604 | h604
          · rcases p572_3 (m.d 0 4) (by simp) with h605 | h605
            · linarith only [h559, h605, hlam]
            · rcases p572_3 (m.d 0 5) (by simp) with h607 | h607
              · linarith only [h560, h607, hlam]
              · rcases h0emin with h609 | h609 | h609 | h609 | h609
                · linarith only [h609, hc03, hlam, p572_1]
                · rcases h3bigk with h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h451, hlam, p611_1]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h451, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p611_1, u3ehi4]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    rcases p611_3 (m.d 0 3) (by simp) with h615 | h615
                    · rcases p611_3 (m.d 1 3) (by simp) with h616 | h616
                      · rcases p611_3 (m.d 2 3) (by simp) with h617 | h617
                        · linarith only [h556, h617, hlam]
                        · linarith only [h568, h617, hlam]
                      · linarith only [h565, h616, hlam]
                    · linarith only [h615, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    rcases p611_3 (m.d 0 3) (by simp) with h622 | h622
                    · rcases p611_3 (m.d 1 3) (by simp) with h623 | h623
                      · rcases p611_3 (m.d 2 3) (by simp) with h624 | h624
                        · linarith only [h556, h624, hlam]
                        · linarith only [h569, h624, hlam]
                      · linarith only [h566, h623, hlam]
                    · linarith only [h622, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h562, hc01, hc12, hlam, hphi, p572_1, p611_1]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p611_1, u3ehi4]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    rcases p611_3 (m.d 0 3) (by simp) with h632 | h632
                    · linarith only [h451, h632, hlam]
                    · linarith only [h559, h632, hlam]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    rcases p611_3 (m.d 0 3) (by simp) with h635 | h635
                    · linarith only [h451, h635, hlam]
                    · linarith only [h560, h635, hlam]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h556, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h562, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p611_1, u3ehi4]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p611_1, u3ehi4]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h559, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h565, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h568, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [hc34, hlam, hphi, p611_1, u3ehi4]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h560, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h566, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h569, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [h571, hlam, p611_0]
                  · have p611_0 := h611c.1
                    have p611_1 := h611c.2.1
                    have p611_2 := h611c.2.2.1
                    have p611_3 := h611c.2.2.2
                    linarith only [hlam, p611_0]
                · rcases h3bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h451, hlam, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h451, h562, h568, h571, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 3) (by simp) with h657 | h657
                    · rcases p653_3 (m.d 1 3) (by simp) with h658 | h658
                      · rcases p653_3 (m.d 2 3) (by simp) with h659 | h659
                        · linarith only [h556, h659, hlam]
                        · linarith only [h568, h659, hlam]
                      · linarith only [h565, h658, hlam]
                    · linarith only [h657, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 3) (by simp) with h664 | h664
                    · rcases p653_3 (m.d 1 3) (by simp) with h665 | h665
                      · rcases p653_3 (m.d 2 3) (by simp) with h666 | h666
                        · linarith only [h556, h666, hlam]
                        · linarith only [h569, h666, hlam]
                      · linarith only [h566, h665, hlam]
                    · linarith only [h664, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h562, h609, hc12, hlam, ht01, p653_1]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p653_1, u3ehi4]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 3) (by simp) with h674 | h674
                    · linarith only [h451, h674, hlam]
                    · linarith only [h559, h674, hlam]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    rcases p653_3 (m.d 0 3) (by simp) with h677 | h677
                    · linarith only [h451, h677, hlam]
                    · linarith only [h560, h677, hlam]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h556, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h562, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p653_1, u3ehi4]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p653_1, u3ehi4]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h559, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h565, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h568, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hc34, hlam, hphi, p653_1, u3ehi4]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h560, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h566, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h569, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [h571, hlam, p653_0]
                  · have p653_0 := h653c.1
                    have p653_1 := h653c.2.1
                    have p653_2 := h653c.2.2.1
                    have p653_3 := h653c.2.2.2
                    linarith only [hlam, p653_0]
                · linarith only [h605, h609, hc03, hlam, p572_1]
                · linarith only [h451, h561, h562, h605, h609, hc12, hlam, ht01, p572_1]
          · linarith only [h451, h604, hlam]
        · linarith only [h0, h603, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h556, hlam, p572_1]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h701 | h701
      · linarith only [h451, h701, hlam]
      · rcases p572_3 (m.d 0 2) (by simp) with h703 | h703
        · rcases p572_3 (m.d 0 3) (by simp) with h704 | h704
          · rcases p572_3 (m.d 0 4) (by simp) with h705 | h705
            · linarith only [h559, h705, hlam]
            · rcases p572_3 (m.d 0 5) (by simp) with h707 | h707
              · linarith only [h560, h707, hlam]
              · rcases h0emin with h709 | h709 | h709 | h709 | h709
                · linarith only [h0, h709, hc12, hlam, ht01]
                · rcases h3bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h451, hlam, p711_1]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p711_1, u3ehi3]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    rcases p711_3 (m.d 0 3) (by simp) with h715 | h715
                    · rcases p711_3 (m.d 1 3) (by simp) with h716 | h716
                      · rcases p711_3 (m.d 2 3) (by simp) with h717 | h717
                        · linarith only [h556, h717, hlam]
                        · linarith only [h568, h717, hlam]
                      · linarith only [h565, h716, hlam]
                    · linarith only [h715, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    rcases p711_3 (m.d 0 3) (by simp) with h722 | h722
                    · rcases p711_3 (m.d 1 3) (by simp) with h723 | h723
                      · rcases p711_3 (m.d 2 3) (by simp) with h724 | h724
                        · linarith only [h556, h724, hlam]
                        · linarith only [h569, h724, hlam]
                      · linarith only [h566, h723, hlam]
                    · linarith only [h722, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h556, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p711_1, u3ehi4]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p711_1, u3ehi4]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    rcases p711_3 (m.d 0 3) (by simp) with h732 | h732
                    · linarith only [h451, h732, hlam]
                    · linarith only [h559, h732, hlam]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    rcases p711_3 (m.d 0 3) (by simp) with h735 | h735
                    · linarith only [h451, h735, hlam]
                    · linarith only [h560, h735, hlam]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h556, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h562, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p711_1, u3ehi4]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p711_1, u3ehi4]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h559, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h565, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h568, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [hc34, hlam, hphi, p711_1, u3ehi4]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h560, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h566, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h569, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [h571, hlam, p711_0]
                  · have p711_0 := h711c.1
                    have p711_1 := h711c.2.1
                    have p711_2 := h711c.2.2.1
                    have p711_3 := h711c.2.2.2
                    linarith only [hlam, p711_0]
                · rcases h3bigk with h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h451, hlam, p753_1]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p753_1, u3ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    rcases p753_3 (m.d 0 3) (by simp) with h757 | h757
                    · rcases p753_3 (m.d 1 3) (by simp) with h758 | h758
                      · rcases p753_3 (m.d 2 3) (by simp) with h759 | h759
                        · linarith only [h556, h759, hlam]
                        · linarith only [h568, h759, hlam]
                      · linarith only [h565, h758, hlam]
                    · linarith only [h757, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    rcases p753_3 (m.d 0 3) (by simp) with h764 | h764
                    · rcases p753_3 (m.d 1 3) (by simp) with h765 | h765
                      · rcases p753_3 (m.d 2 3) (by simp) with h766 | h766
                        · linarith only [h556, h766, hlam]
                        · linarith only [h569, h766, hlam]
                      · linarith only [h566, h765, hlam]
                    · linarith only [h764, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h562, h709, hc12, hlam, ht01, p753_1]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p753_1, u3ehi4]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    rcases p753_3 (m.d 0 3) (by simp) with h774 | h774
                    · linarith only [h451, h774, hlam]
                    · linarith only [h559, h774, hlam]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    rcases p753_3 (m.d 0 3) (by simp) with h777 | h777
                    · linarith only [h451, h777, hlam]
                    · linarith only [h560, h777, hlam]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h556, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h562, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p753_1, u3ehi4]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p753_1, u3ehi4]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h559, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h565, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h568, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hc34, hlam, hphi, p753_1, u3ehi4]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h560, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h566, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h569, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h571, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                · linarith only [h709, hc03, hlam, p572_1]
                · linarith only [h561, h709, hc03, hlam, p572_1]
          · linarith only [h559, h704, hlam]
        · linarith only [h557, h703, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h799 | h799
      · linarith only [h451, h799, hlam]
      · rcases p572_3 (m.d 0 2) (by simp) with h801 | h801
        · rcases p572_3 (m.d 0 3) (by simp) with h802 | h802
          · rcases p572_3 (m.d 0 4) (by simp) with h803 | h803
            · linarith only [h559, h803, hlam]
            · linarith only [h561, h803, hlam]
          · linarith only [h560, h802, hlam]
        · linarith only [h558, h801, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h808 | h808
      · linarith only [h808, hlam, p572_0]
      · rcases p572_3 (m.d 0 2) (by simp) with h810 | h810
        · rcases p572_3 (m.d 0 3) (by simp) with h811 | h811
          · rcases p572_3 (m.d 0 4) (by simp) with h812 | h812
            · rcases p572_3 (m.d 0 5) (by simp) with h813 | h813
              · linarith only [h561, h813, hlam]
              · rcases h0emin with h815 | h815 | h815 | h815 | h815
                · linarith only [h815, hc04, hlam, p572_1]
                · rcases h3bigk with h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h451, hlam, p817_1]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p817_1, u3ehi3]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    rcases p817_3 (m.d 0 3) (by simp) with h821 | h821
                    · rcases p817_3 (m.d 1 3) (by simp) with h822 | h822
                      · rcases p817_3 (m.d 2 3) (by simp) with h823 | h823
                        · linarith only [h556, h823, hlam]
                        · linarith only [h568, h823, hlam]
                      · linarith only [h565, h822, hlam]
                    · linarith only [h821, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    rcases p817_3 (m.d 0 3) (by simp) with h828 | h828
                    · rcases p817_3 (m.d 1 3) (by simp) with h829 | h829
                      · rcases p817_3 (m.d 2 3) (by simp) with h830 | h830
                        · linarith only [h556, h830, hlam]
                        · linarith only [h569, h830, hlam]
                      · linarith only [h566, h829, hlam]
                    · linarith only [h828, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h559, h562, hc01, hc12, hlam, hphi, p572_1, p817_1]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p817_1, u3ehi4]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    rcases p817_3 (m.d 0 3) (by simp) with h838 | h838
                    · linarith only [h451, h838, hlam]
                    · linarith only [h559, h838, hlam]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    rcases p817_3 (m.d 0 3) (by simp) with h841 | h841
                    · linarith only [h451, h841, hlam]
                    · linarith only [h560, h841, hlam]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h556, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h562, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p817_1, u3ehi4]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p817_1, u3ehi4]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h559, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h565, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h568, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [hc34, hlam, hphi, p817_1, u3ehi4]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h560, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h566, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h569, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [h571, hlam, p817_0]
                  · have p817_0 := h817c.1
                    have p817_1 := h817c.2.1
                    have p817_2 := h817c.2.2.1
                    have p817_3 := h817c.2.2.2
                    linarith only [hlam, p817_0]
                · rcases h3bigk with h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h451, hlam, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1, u3ehi3]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    rcases p859_3 (m.d 0 3) (by simp) with h863 | h863
                    · rcases p859_3 (m.d 1 3) (by simp) with h864 | h864
                      · rcases p859_3 (m.d 2 3) (by simp) with h865 | h865
                        · linarith only [h556, h865, hlam]
                        · linarith only [h568, h865, hlam]
                      · linarith only [h565, h864, hlam]
                    · linarith only [h863, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    rcases p859_3 (m.d 0 3) (by simp) with h870 | h870
                    · rcases p859_3 (m.d 1 3) (by simp) with h871 | h871
                      · rcases p859_3 (m.d 2 3) (by simp) with h872 | h872
                        · linarith only [h556, h872, hlam]
                        · linarith only [h569, h872, hlam]
                      · linarith only [h566, h871, hlam]
                    · linarith only [h870, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h562, h815, hc12, hlam, ht01, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    rcases p859_3 (m.d 0 3) (by simp) with h880 | h880
                    · linarith only [h451, h880, hlam]
                    · linarith only [h559, h880, hlam]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    rcases p859_3 (m.d 0 3) (by simp) with h883 | h883
                    · linarith only [h451, h883, hlam]
                    · linarith only [h560, h883, hlam]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h556, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h562, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h559, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h565, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h568, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hc34, hlam, hphi, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h560, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h566, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h569, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h571, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                · rcases h3bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h451, hlam, p901_1]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p901_1, u3ehi3]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    rcases p901_3 (m.d 0 3) (by simp) with h905 | h905
                    · rcases p901_3 (m.d 1 3) (by simp) with h906 | h906
                      · rcases p901_3 (m.d 2 3) (by simp) with h907 | h907
                        · linarith only [h556, h907, hlam]
                        · linarith only [h568, h907, hlam]
                      · linarith only [h565, h906, hlam]
                    · linarith only [h905, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    rcases p901_3 (m.d 0 3) (by simp) with h912 | h912
                    · rcases p901_3 (m.d 1 3) (by simp) with h913 | h913
                      · rcases p901_3 (m.d 2 3) (by simp) with h914 | h914
                        · linarith only [h556, h914, hlam]
                        · linarith only [h569, h914, hlam]
                      · linarith only [h566, h913, hlam]
                    · linarith only [h912, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h556, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p901_1, u3ehi4]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p901_1, u3ehi4]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    rcases p901_3 (m.d 0 3) (by simp) with h922 | h922
                    · linarith only [h451, h922, hlam]
                    · linarith only [h559, h922, hlam]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    rcases p901_3 (m.d 0 3) (by simp) with h925 | h925
                    · linarith only [h451, h925, hlam]
                    · linarith only [h560, h925, hlam]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h556, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h562, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p901_1, u3ehi4]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p901_1, u3ehi4]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h559, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h565, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h568, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [hc34, hlam, hphi, p901_1, u3ehi4]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h560, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h566, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h569, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [h571, hlam, p901_0]
                  · have p901_0 := h901c.1
                    have p901_1 := h901c.2.1
                    have p901_2 := h901c.2.2.1
                    have p901_3 := h901c.2.2.2
                    linarith only [hlam, p901_0]
                · linarith only [h559, h813, h815, hc03, hlam, p572_1]
            · linarith only [h812, hlam, p572_0]
          · linarith only [h451, h811, hlam]
        · linarith only [h0, h810, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h557, hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h559, hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h950 | h950
      · linarith only [h451, h558, h562, h950, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u2ehi4]
      · rcases p572_3 (m.d 0 2) (by simp) with h952 | h952
        · rcases p572_3 (m.d 0 3) (by simp) with h953 | h953
          · rcases p572_3 (m.d 0 4) (by simp) with h954 | h954
            · rcases p572_3 (m.d 0 5) (by simp) with h955 | h955
              · linarith only [h561, h955, hlam]
              · rcases h0emin with h957 | h957 | h957 | h957 | h957
                · linarith only [h950, h957, hc04, hlam, p572_1]
                · rcases h3bigk with h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h451, hlam, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p959_1, u3ehi3]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    rcases p959_3 (m.d 0 3) (by simp) with h963 | h963
                    · rcases p959_3 (m.d 1 3) (by simp) with h964 | h964
                      · rcases p959_3 (m.d 2 3) (by simp) with h965 | h965
                        · linarith only [h556, h965, hlam]
                        · linarith only [h568, h965, hlam]
                      · linarith only [h565, h964, hlam]
                    · linarith only [h963, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    rcases p959_3 (m.d 0 3) (by simp) with h970 | h970
                    · rcases p959_3 (m.d 1 3) (by simp) with h971 | h971
                      · rcases p959_3 (m.d 2 3) (by simp) with h972 | h972
                        · linarith only [h556, h972, hlam]
                        · linarith only [h569, h972, hlam]
                      · linarith only [h566, h971, hlam]
                    · linarith only [h970, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h559, h562, h950, hc01, hc12, hlam, hphi, p572_1, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p959_1, u3ehi4]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    rcases p959_3 (m.d 0 3) (by simp) with h980 | h980
                    · linarith only [h451, h980, hlam]
                    · linarith only [h559, h980, hlam]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    rcases p959_3 (m.d 0 3) (by simp) with h983 | h983
                    · linarith only [h451, h983, hlam]
                    · linarith only [h560, h983, hlam]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h556, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h562, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p959_1, u3ehi4]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p959_1, u3ehi4]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h559, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h565, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h568, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hc34, hlam, hphi, p959_1, u3ehi4]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h560, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h566, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h569, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h571, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                · rcases h3bigk with h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h451, hlam, p1001_1]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1001_1, u3ehi3]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    rcases p1001_3 (m.d 0 3) (by simp) with h1005 | h1005
                    · rcases p1001_3 (m.d 1 3) (by simp) with h1006 | h1006
                      · rcases p1001_3 (m.d 2 3) (by simp) with h1007 | h1007
                        · linarith only [h1007, h556, hlam]
                        · linarith only [h1007, h568, hlam]
                      · linarith only [h1006, h565, hlam]
                    · linarith only [h1005, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    rcases p1001_3 (m.d 0 3) (by simp) with h1012 | h1012
                    · rcases p1001_3 (m.d 1 3) (by simp) with h1013 | h1013
                      · rcases p1001_3 (m.d 2 3) (by simp) with h1014 | h1014
                        · linarith only [h1014, h556, hlam]
                        · linarith only [h1014, h569, hlam]
                      · linarith only [h1013, h566, hlam]
                    · linarith only [h1012, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h562, h957, hc12, hlam, ht01, p1001_1]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1001_1, u3ehi4]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    rcases p1001_3 (m.d 0 3) (by simp) with h1022 | h1022
                    · linarith only [h1022, h451, hlam]
                    · linarith only [h1022, h559, hlam]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    rcases p1001_3 (m.d 0 3) (by simp) with h1025 | h1025
                    · linarith only [h1025, h451, hlam]
                    · linarith only [h1025, h560, hlam]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h556, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h562, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1001_1, u3ehi4]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1001_1, u3ehi4]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h559, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h565, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h568, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [hc34, hlam, hphi, p1001_1, u3ehi4]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h560, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h566, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h569, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [h571, hlam, p1001_0]
                  · have p1001_0 := h1001c.1
                    have p1001_1 := h1001c.2.1
                    have p1001_2 := h1001c.2.2.1
                    have p1001_3 := h1001c.2.2.2
                    linarith only [hlam, p1001_0]
                · rcases h3bigk with h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h451, hlam, p1043_1]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1043_1, u3ehi3]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    rcases p1043_3 (m.d 0 3) (by simp) with h1047 | h1047
                    · rcases p1043_3 (m.d 1 3) (by simp) with h1048 | h1048
                      · rcases p1043_3 (m.d 2 3) (by simp) with h1049 | h1049
                        · linarith only [h1049, h556, hlam]
                        · linarith only [h1049, h568, hlam]
                      · linarith only [h1048, h565, hlam]
                    · linarith only [h1047, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    rcases p1043_3 (m.d 0 3) (by simp) with h1054 | h1054
                    · rcases p1043_3 (m.d 1 3) (by simp) with h1055 | h1055
                      · rcases p1043_3 (m.d 2 3) (by simp) with h1056 | h1056
                        · linarith only [h1056, h556, hlam]
                        · linarith only [h1056, h569, hlam]
                      · linarith only [h1055, h566, hlam]
                    · linarith only [h1054, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h556, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1043_1, u3ehi4]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1043_1, u3ehi4]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    rcases p1043_3 (m.d 0 3) (by simp) with h1064 | h1064
                    · linarith only [h1064, h451, hlam]
                    · linarith only [h1064, h559, hlam]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    rcases p1043_3 (m.d 0 3) (by simp) with h1067 | h1067
                    · linarith only [h1067, h451, hlam]
                    · linarith only [h1067, h560, hlam]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h556, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h562, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1043_1, u3ehi4]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1043_1, u3ehi4]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h559, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h565, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h568, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [hc34, hlam, hphi, p1043_1, u3ehi4]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h560, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h566, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h569, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [h571, hlam, p1043_0]
                  · have p1043_0 := h1043c.1
                    have p1043_1 := h1043c.2.1
                    have p1043_2 := h1043c.2.2.1
                    have p1043_3 := h1043c.2.2.2
                    linarith only [hlam, p1043_0]
                · linarith only [h559, h957, hc03, hlam, p572_1]
            · linarith only [h561, h954, hlam]
          · linarith only [h560, h953, hlam]
        · linarith only [h558, h952, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      rcases p572_3 (m.d 0 1) (by simp) with h1089 | h1089
      · linarith only [h1089, hlam, p572_0]
      · rcases p572_3 (m.d 0 2) (by simp) with h1091 | h1091
        · rcases p572_3 (m.d 0 3) (by simp) with h1092 | h1092
          · rcases p572_3 (m.d 0 4) (by simp) with h1093 | h1093
            · rcases p572_3 (m.d 0 5) (by simp) with h1094 | h1094
              · rcases h0emin with h1095 | h1095 | h1095 | h1095 | h1095
                · linarith only [h0, h1095, hc12, hlam, ht01]
                · rcases h3bigk with h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h451, hlam, p1097_1]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1097_1, u3ehi3]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    rcases p1097_3 (m.d 0 3) (by simp) with h1101 | h1101
                    · rcases p1097_3 (m.d 1 3) (by simp) with h1102 | h1102
                      · rcases p1097_3 (m.d 2 3) (by simp) with h1103 | h1103
                        · linarith only [h1103, h556, hlam]
                        · linarith only [h1103, h568, hlam]
                      · linarith only [h1102, h565, hlam]
                    · linarith only [h1101, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    rcases p1097_3 (m.d 0 3) (by simp) with h1108 | h1108
                    · rcases p1097_3 (m.d 1 3) (by simp) with h1109 | h1109
                      · rcases p1097_3 (m.d 2 3) (by simp) with h1110 | h1110
                        · linarith only [h1110, h556, hlam]
                        · linarith only [h1110, h569, hlam]
                      · linarith only [h1109, h566, hlam]
                    · linarith only [h1108, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h556, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1097_1, u3ehi4]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1097_1, u3ehi4]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    rcases p1097_3 (m.d 0 3) (by simp) with h1118 | h1118
                    · linarith only [h1118, h451, hlam]
                    · linarith only [h1118, h559, hlam]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    rcases p1097_3 (m.d 0 3) (by simp) with h1121 | h1121
                    · linarith only [h1121, h451, hlam]
                    · linarith only [h1121, h560, hlam]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h556, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h562, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1097_1, u3ehi4]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1097_1, u3ehi4]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h559, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h565, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h568, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [hc34, hlam, hphi, p1097_1, u3ehi4]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h560, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h566, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h569, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [h571, hlam, p1097_0]
                  · have p1097_0 := h1097c.1
                    have p1097_1 := h1097c.2.1
                    have p1097_2 := h1097c.2.2.1
                    have p1097_3 := h1097c.2.2.2
                    linarith only [hlam, p1097_0]
                · rcases h3bigk with h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h451, hlam, p1139_1]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1139_1, u3ehi3]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    rcases p1139_3 (m.d 0 3) (by simp) with h1143 | h1143
                    · rcases p1139_3 (m.d 1 3) (by simp) with h1144 | h1144
                      · rcases p1139_3 (m.d 2 3) (by simp) with h1145 | h1145
                        · linarith only [h1145, h556, hlam]
                        · linarith only [h1145, h568, hlam]
                      · linarith only [h1144, h565, hlam]
                    · linarith only [h1143, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    rcases p1139_3 (m.d 0 3) (by simp) with h1150 | h1150
                    · rcases p1139_3 (m.d 1 3) (by simp) with h1151 | h1151
                      · rcases p1139_3 (m.d 2 3) (by simp) with h1152 | h1152
                        · linarith only [h1152, h556, hlam]
                        · linarith only [h1152, h569, hlam]
                      · linarith only [h1151, h566, hlam]
                    · linarith only [h1150, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h1095, h562, hc12, hlam, ht01, p1139_1]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1139_1, u3ehi4]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    rcases p1139_3 (m.d 0 3) (by simp) with h1160 | h1160
                    · linarith only [h1160, h451, hlam]
                    · linarith only [h1160, h559, hlam]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    rcases p1139_3 (m.d 0 3) (by simp) with h1163 | h1163
                    · linarith only [h1163, h451, hlam]
                    · linarith only [h1163, h560, hlam]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h556, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h562, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1139_1, u3ehi4]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1139_1, u3ehi4]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h559, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h565, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h568, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [hc34, hlam, hphi, p1139_1, u3ehi4]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h560, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h566, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h569, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [h571, hlam, p1139_0]
                  · have p1139_0 := h1139c.1
                    have p1139_1 := h1139c.2.1
                    have p1139_2 := h1139c.2.2.1
                    have p1139_3 := h1139c.2.2.2
                    linarith only [hlam, p1139_0]
                · rcases h3bigk with h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h451, hlam, p1181_1]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi3]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    rcases p1181_3 (m.d 0 3) (by simp) with h1185 | h1185
                    · rcases p1181_3 (m.d 1 3) (by simp) with h1186 | h1186
                      · rcases p1181_3 (m.d 2 3) (by simp) with h1187 | h1187
                        · linarith only [h1187, h556, hlam]
                        · linarith only [h1187, h568, hlam]
                      · linarith only [h1186, h565, hlam]
                    · linarith only [h1185, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    rcases p1181_3 (m.d 0 3) (by simp) with h1192 | h1192
                    · rcases p1181_3 (m.d 1 3) (by simp) with h1193 | h1193
                      · rcases p1181_3 (m.d 2 3) (by simp) with h1194 | h1194
                        · linarith only [h1194, h556, hlam]
                        · linarith only [h1194, h569, hlam]
                      · linarith only [h1193, h566, hlam]
                    · linarith only [h1192, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h556, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi4]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi4]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    rcases p1181_3 (m.d 0 3) (by simp) with h1202 | h1202
                    · linarith only [h1202, h451, hlam]
                    · linarith only [h1202, h559, hlam]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    rcases p1181_3 (m.d 0 3) (by simp) with h1205 | h1205
                    · linarith only [h1205, h451, hlam]
                    · linarith only [h1205, h560, hlam]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h556, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h562, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi4]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi4]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h559, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h565, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h568, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [hc34, hlam, hphi, p1181_1, u3ehi4]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h560, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h566, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h569, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [h571, hlam, p1181_0]
                  · have p1181_0 := h1181c.1
                    have p1181_1 := h1181c.2.1
                    have p1181_2 := h1181c.2.2.1
                    have p1181_3 := h1181c.2.2.2
                    linarith only [hlam, p1181_0]
                · rcases h3bigk with h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h451, hlam, p1223_1]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1223_1, u3ehi3]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    rcases p1223_3 (m.d 0 3) (by simp) with h1227 | h1227
                    · rcases p1223_3 (m.d 1 3) (by simp) with h1228 | h1228
                      · rcases p1223_3 (m.d 2 3) (by simp) with h1229 | h1229
                        · linarith only [h1229, h556, hlam]
                        · linarith only [h1229, h568, hlam]
                      · linarith only [h1228, h565, hlam]
                    · linarith only [h1227, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    rcases p1223_3 (m.d 0 3) (by simp) with h1234 | h1234
                    · rcases p1223_3 (m.d 1 3) (by simp) with h1235 | h1235
                      · rcases p1223_3 (m.d 2 3) (by simp) with h1236 | h1236
                        · linarith only [h1236, h556, hlam]
                        · linarith only [h1236, h569, hlam]
                      · linarith only [h1235, h566, hlam]
                    · linarith only [h1234, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h556, h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1223_1, u3ehi4]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h562, h568, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1223_1, u3ehi4]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    rcases p1223_3 (m.d 0 3) (by simp) with h1244 | h1244
                    · linarith only [h1244, h451, hlam]
                    · linarith only [h1244, h559, hlam]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    rcases p1223_3 (m.d 0 3) (by simp) with h1247 | h1247
                    · linarith only [h1247, h451, hlam]
                    · linarith only [h1247, h560, hlam]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h556, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h562, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h0, h556, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1223_1, u3ehi4]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1223_1, u3ehi4]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h559, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h565, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h568, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [hc34, hlam, hphi, p1223_1, u3ehi4]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h560, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h566, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h569, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [h571, hlam, p1223_0]
                  · have p1223_0 := h1223c.1
                    have p1223_1 := h1223c.2.1
                    have p1223_2 := h1223c.2.2.1
                    have p1223_3 := h1223c.2.2.2
                    linarith only [hlam, p1223_0]
              · linarith only [h1094, hlam, p572_0]
            · linarith only [h1093, h561, hlam, p572_1]
          · linarith only [h1092, h451, hlam]
        · linarith only [h0, h1091, hlam]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h558, hlam, p572_1]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h560, hlam, p572_0]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [h561, hlam, p572_1]
    · have p572_0 := h572c.1
      have p572_1 := h572c.2.1
      have p572_2 := h572c.2.2.1
      have p572_3 := h572c.2.2.2
      linarith only [hlam, p572_0]
  · linarith only [h0, h556, h568, h570, h571, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]

end R2N4
