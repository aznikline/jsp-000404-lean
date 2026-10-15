import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3494000 in
set_option maxHeartbeats 3494000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_R_M_IR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h432 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h612 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h613 | h613
  · rcases m.htr 0 2 3 (by decide) (by decide) with h614 | h614
    · rcases m.htr 0 2 4 (by decide) (by decide) with h615 | h615
      · rcases m.htr 0 2 5 (by decide) (by decide) with h616 | h616
        · rcases m.htr 0 3 4 (by decide) (by decide) with h617 | h617
          · rcases m.htr 0 3 5 (by decide) (by decide) with h618 | h618
            · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
              · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h622 | h622
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h625 | h625
                          · linarith only [h432, h612, h620, h625, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h432, h612, h619, h620, h625, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h432, h613, h624, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h432, h613, h623, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h432, h612, h620, h621, h622, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h432, h612, h620, h621, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h612, h614, h619, h620, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h633 | h633
                · rcases m.htr 1 2 4 (by decide) (by decide) with h634 | h634
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                          · linarith only [h612, h619, h638, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                                · linarith only [h612, h619, h634, h642, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h644 | h644
                                  · linarith only [h612, h619, h634, h644, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h1bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h0, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h432, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h0, h634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p646_1, u2ehi3]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h0, h634, h638, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p646_1, u2ehi3]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h612, h634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p646_1, u2ehi3]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h432, h613, h634, h638, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p646_1, u2ehi3]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      rcases p646_3 (m.d 0 1) (by simp) with h655 | h655
                                      · linarith only [h0, h655, hlam]
                                      · linarith only [h612, h655, hlam]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      rcases p646_3 (m.d 0 1) (by simp) with h658 | h658
                                      · linarith only [h0, h658, hlam]
                                      · linarith only [h613, h658, hlam]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h613, h634, h638, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p646_1, u2ehi3]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h633, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      rcases p646_3 (m.d 0 1) (by simp) with h664 | h664
                                      · linarith only [h432, h664, hlam]
                                      · linarith only [h612, h664, hlam]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      rcases p646_3 (m.d 0 1) (by simp) with h667 | h667
                                      · linarith only [h432, h667, hlam]
                                      · linarith only [h613, h667, hlam]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h612, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h634, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h636, hlam, p646_1]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h638, hlam, p646_1]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h613, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h635, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h637, hlam, p646_0]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [h613, h634, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p646_1, u2ehi3]
                                    · have p646_0 := h646c.1
                                      have p646_1 := h646c.2.1
                                      have p646_2 := h646c.2.2.1
                                      have p646_3 := h646c.2.2.2
                                      linarith only [hlam, p646_0]
                              · linarith only [h432, h613, h633, h637, h641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h617, h619, h640, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h432, h613, h637, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h432, h612, h617, h634, h636, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h432, h612, h633, h634, h635, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h432, h612, h633, h634, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h612, h614, h633, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h432, h613, h618, hlam]
          · linarith only [h432, h612, h617, hlam]
        · linarith only [h614, h616, hc25, hlam, hphi, u2ehi2]
      · linarith only [h614, h615, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h691 | h691
      · linarith only [h614, h691, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h612, h691, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h694 | h694
    · rcases m.htr 0 2 4 (by decide) (by decide) with h695 | h695
      · rcases m.htr 0 2 5 (by decide) (by decide) with h696 | h696
        · rcases m.htr 0 3 4 (by decide) (by decide) with h697 | h697
          · rcases m.htr 0 3 5 (by decide) (by decide) with h698 | h698
            · rcases m.htr 0 4 5 (by decide) (by decide) with h699 | h699
              · linarith only [h612, h613, h699, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h701 | h701
                · rcases m.htr 1 2 4 (by decide) (by decide) with h702 | h702
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h703 | h703
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h704 | h704
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h705 | h705
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h706 | h706
                          · linarith only [h612, h613, h694, h698, h699, h706, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h612, h613, h702, h706, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · linarith only [h0, h432, h612, h694, h698, h702, h705, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h432, h612, h702, h704, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h696, h703, hlam]
                  · linarith only [h0, h694, h702, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h694, h701, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h714 | h714
              · linarith only [h612, h613, h714, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h716 | h716
                · rcases m.htr 1 2 4 (by decide) (by decide) with h717 | h717
                  · linarith only [h432, h612, h698, h717, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h432, h612, h716, h717, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h694, h716, hlam]
          · linarith only [h432, h612, h697, hlam]
        · linarith only [h694, h696, hc25, hlam, hphi, u2ehi2]
      · linarith only [h694, h695, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h724 | h724
      · linarith only [h694, h724, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h612, h724, hlam]

end R2N4
