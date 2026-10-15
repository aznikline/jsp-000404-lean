import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_60S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3432000 in
theorem r1l7_11_13_25_L_0_L_R_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h578 | h578
  · rcases m.htr 0 3 5 (by decide) (by decide) with h579 | h579
    · rcases m.htr 0 4 5 (by decide) (by decide) with h580 | h580
      · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
        · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
          · rcases m.htr 1 3 5 (by decide) (by decide) with h583 | h583
            · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
              · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h587 | h587
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h588 | h588
                      · rcases h5bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h578, h585, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h578, h585, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h578, h585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p589_1, u3ehi4]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h578, h585, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h0, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p589_1, u1elo4]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p589_1, u1elo0, u3ehi4]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p589_1, u1elo0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h578, hlam, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h581, hlam, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p589_1, u3ehi4]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h1, h578, h585, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h579, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h583, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h586, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h579, hc03, hc45, hlam, hphi, ht0b, ht5b, p589_1]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h580, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h584, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h587, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [h588, hlam, p589_0]
                        · have p589_0 := h589c.1
                          have p589_1 := h589c.2.1
                          have p589_2 := h589c.2.2.1
                          have p589_3 := h589c.2.2.2
                          linarith only [hlam, p589_0]
                      · linarith only [h584, h588, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                    · linarith only [h1, h582, h584, h587, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h1, h578, h579, h585, h586, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h582, h585, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                · rcases m.htr 2 3 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h621 | h621
                    · linarith only [h581, h582, h584, h621, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                    · linarith only [h1, h578, h580, h621, hlam]
                  · linarith only [h1, h578, h580, h582, h584, h619, h620, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h578, h580, h582, h584, h619, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h582, h583, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h627 | h627
            · linarith only [h582, h627, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h629 | h629
              · rcases m.htr 2 3 4 (by decide) (by decide) with h630 | h630
                · rcases m.htr 2 3 5 (by decide) (by decide) with h631 | h631
                  · linarith only [h0, h581, h627, h631, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · linarith only [h630, h631, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h578, h579, h627, h630, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
                · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                  · linarith only [h1, h578, h627, h635, h636, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h635, h636, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h578, h580, h582, h629, h635, hc34, hlam, hphi, u3ehi1]
        · linarith only [h1, h578, h581, hc12, hc24, hlam, hphi]
      · linarith only [h1, h578, h580, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
      · rcases m.htr 1 2 5 (by decide) (by decide) with h643 | h643
        · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
          · rcases m.htr 1 3 5 (by decide) (by decide) with h645 | h645
            · linarith only [h579, h645, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h644, h645, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
            · linarith only [h644, h648, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h650 | h650
              · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
                  · linarith only [h643, h648, h652, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                  · linarith only [h651, h652, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h655 | h655
                  · linarith only [h651, h655, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h578, h651, h655, hc34, hlam, hphi, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h658 | h658
                · rcases m.htr 2 3 5 (by decide) (by decide) with h659 | h659
                  · linarith only [h1, h578, h579, h642, h644, h650, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h658, h659, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h578, h642, h644, h650, h658, hc34, hlam, hphi, u3ehi1]
        · linarith only [h1, h578, h643, hc12, hc24, hlam, hphi]
      · linarith only [h1, h578, h642, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h665 | h665
    · rcases m.htr 0 4 5 (by decide) (by decide) with h666 | h666
      · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
        · linarith only [h0, h578, h667, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
          · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
            · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
              · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                · rcases m.htr 2 3 5 (by decide) (by decide) with h673 | h673
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h674 | h674
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                      · rcases h5bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p676_1, u1elo0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h578, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p676_1, u1elo0, u3ehi4]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p676_1, u1elo0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h0, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h667, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p676_1, u1elo4, u3ehi4]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p676_1, u1elo0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h578, hc02, hc25, hlam, hphi, p676_1]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h667, hc12, hc25, hlam, hphi, p676_1]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h673, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p676_1, u3ehi4]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          rcases p676_3 (m.d 0 5) (by simp) with h691 | h691
                          · linarith only [h578, h691, hlam]
                          · linarith only [h666, h691, hlam]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h665, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h670, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h673, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h665, hc03, hc45, hlam, hphi, ht0b, ht5b, p676_1]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h666, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h671, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h674, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [h675, hlam, p676_0]
                        · have p676_0 := h676c.1
                          have p676_1 := h676c.2.1
                          have p676_2 := h676c.2.2.1
                          have p676_3 := h676c.2.2.2
                          linarith only [hlam, p676_0]
                      · linarith only [h671, h675, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                    · linarith only [h1, h669, h671, h674, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h670, h673, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                · linarith only [h669, h672, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h708 | h708
                · rcases m.htr 2 3 5 (by decide) (by decide) with h709 | h709
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h710 | h710
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h711 | h711
                      · linarith only [h669, h671, h711, hlam]
                      · rcases h5bigk with h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h670, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p713_1, u3ehi4]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h578, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p713_1, u1elo0, u3ehi4]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h669, h671, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p713_1, u1elo0, u3ehi3]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h667, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p713_1, u1elo4, u3ehi4]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h671, hlam, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h578, hc02, hc25, hlam, hphi, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h667, hc12, hc25, hlam, hphi, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h709, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p713_1, u3ehi4]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h669, h671, h708, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p713_1, u3ehi3]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h665, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h670, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h709, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h711, hlam, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h666, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h666, h669, h671, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p713_1, u3ehi3]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h710, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h1, h666, h708, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p713_1, u3ehi4]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                    · linarith only [h1, h666, h710, hlam]
                  · linarith only [h1, h665, h666, h708, h709, hlam]
                · linarith only [h1, h666, h669, h671, h708, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h669, h670, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
            · linarith only [h669, h743, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h745 | h745
              · rcases m.htr 2 3 4 (by decide) (by decide) with h746 | h746
                · rcases m.htr 2 3 5 (by decide) (by decide) with h747 | h747
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h748 | h748
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h749 | h749
                      · rcases h5bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p750_1, u1elo0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h578, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h743, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p750_1, u1elo0, u3ehi1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p750_1, u1elo0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h667, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h743, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p750_1, u1elo4]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h578, hc02, hc25, hlam, hphi, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h667, hc12, hc25, hlam, hphi, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h743, h747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u3ehi1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          rcases p750_3 (m.d 0 5) (by simp) with h765 | h765
                          · linarith only [h578, h765, hlam]
                          · linarith only [h666, h765, hlam]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h665, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h665, h743, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1, u3ehi1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h747, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h665, hc45, hlam, hphi, ht01, ht0b, ht5b, p750_1, u1elo0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h666, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h745, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h748, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h749, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                      · linarith only [h1, h666, h669, h746, h749, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h745, h748, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h665, h746, h747, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h781 | h781
                  · linarith only [h746, h781, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h578, h665, h781, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h784 | h784
                · rcases m.htr 2 3 5 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h787 | h787
                      · linarith only [h669, h745, h784, h787, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h666, h669, h787, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h666, h786, hlam]
                  · linarith only [h1, h665, h666, h784, h785, hlam]
                · linarith only [h1, h666, h669, h745, h784, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h793 | h793
        · linarith only [h0, h578, h793, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
          · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
            · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
              · linarith only [h0, h666, h797, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
                      · linarith only [h795, h797, h802, hlam]
                      · rcases h5bigk with h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h666, h799, h801, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h578, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h666, h799, h801, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p804_1, u3ehi4]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h666, hlam, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h0, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h793, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p804_1, u1elo4, u3ehi4]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h797, hlam, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h578, hc02, hc25, hlam, hphi, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h793, hc12, hc25, hlam, hphi, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h800, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p804_1, u3ehi4]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h1, h666, h799, h801, hc02, hc23, hlam, hphi, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h665, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h796, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h800, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h802, hlam, p804_1]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h0, h795, h797, hc45, hlam, hphi, ht34, p804_1, u3ehi3]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h795, h797, hc45, hlam, hphi, ht34, p804_1, u3ehi3]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h801, hlam, p804_0]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [h799, h801, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p804_1, u3ehi4]
                        · have p804_0 := h804c.1
                          have p804_1 := h804c.2.1
                          have p804_2 := h804c.2.2.1
                          have p804_3 := h804c.2.2.2
                          linarith only [hlam, p804_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                      · linarith only [h0, h795, h797, h801, h830, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases h5bigk with h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p832_1, u1elo0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h578, hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h830, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p832_1, u3ehi3]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h666, hlam, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h0, hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h793, hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h830, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p832_1, u1elo4, u3ehi3]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h797, hlam, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h578, h801, hc02, hc45, hlam, hphi, ht23, ht34, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h793, h801, hc12, hc45, hlam, hphi, ht23, ht34, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h801, h830, hc45, hlam, hphi, ht34, p832_1, u3ehi3]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h801, hlam, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h665, hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h796, hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h800, hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [hlam, p832_0]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h830, hlam, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h0, h796, h830, hc45, hlam, hphi, ht34, p832_1, u3ehi3]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h796, h830, hc45, hlam, hphi, ht34, p832_1, u3ehi3]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h578, hc02, hc45, hlam, hphi, ht23, ht34, p832_1]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [h830, hc45, hlam, hphi, ht34, p832_1, u3ehi3]
                        · have p832_0 := h832c.1
                          have p832_1 := h832c.2.1
                          have p832_2 := h832c.2.2.1
                          have p832_3 := h832c.2.2.2
                          linarith only [hlam, p832_0]
                  · linarith only [h0, h796, h800, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                · linarith only [h795, h799, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
            · linarith only [h795, h796, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h861 | h861
            · linarith only [h795, h861, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h863 | h863
              · linarith only [h665, h666, h861, h863, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
                · rcases m.htr 2 3 5 (by decide) (by decide) with h866 | h866
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h867 | h867
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h868 | h868
                      · linarith only [h665, h666, h861, h865, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h795, h868, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h795, h865, h867, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h665, h795, h865, h866, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
                  · linarith only [h865, h873, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h578, h665, h873, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h876 | h876
      · rcases m.htr 1 2 5 (by decide) (by decide) with h877 | h877
        · linarith only [h0, h578, h877, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
          · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
            · linarith only [h665, h880, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h879, h880, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h883 | h883
            · linarith only [h879, h883, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h885 | h885
              · rcases m.htr 2 3 4 (by decide) (by decide) with h886 | h886
                · rcases m.htr 2 3 5 (by decide) (by decide) with h887 | h887
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h889 | h889
                      · rcases h5bigk with h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h876, h883, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p890_1, u3ehi1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h578, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h665, hlam, p890_1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p890_1, u1elo0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h0, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h877, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h883, hlam, p890_1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h885, hc45, hlam, hphi, ht01, ht0b, ht5b, p890_1, u1elo3]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h578, h886, h888, hc02, hc23, hlam, hphi, p890_1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h877, h886, h888, hc12, hc23, hlam, hphi, p890_1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h665, h886, h888, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p890_1, u3ehi0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          rcases p890_3 (m.d 0 5) (by simp) with h905 | h905
                          · linarith only [h578, h905, hlam]
                          · linarith only [h876, h905, hlam]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h0, h883, hc35, hlam, hphi, p890_1, u3ehi1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h883, hc35, hlam, hphi, p890_1, u3ehi1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h887, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h886, h889, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p890_1]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h876, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h885, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h888, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [h889, hlam, p890_0]
                        · have p890_0 := h890c.1
                          have p890_1 := h890c.2.1
                          have p890_2 := h890c.2.2.1
                          have p890_3 := h890c.2.2.2
                          linarith only [hlam, p890_0]
                      · linarith only [h1, h876, h879, h886, h889, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h879, h885, h886, h888, hc02, hc23, hlam, hphi]
                  · linarith only [h886, h887, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h921 | h921
                  · linarith only [h886, h921, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h923 | h923
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h924 | h924
                      · rcases h5bigk with h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p925_1, u1elo0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h578, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h665, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p925_1, u1elo0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h877, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h883, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p925_1, u1elo4]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h578, h886, h923, hc02, hc34, hlam, hphi, ht23, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h877, h886, h923, hc12, hc34, hlam, hphi, ht23, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h921, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          rcases p925_3 (m.d 0 5) (by simp) with h940 | h940
                          · linarith only [h578, h940, hlam]
                          · linarith only [h876, h940, hlam]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, h883, h924, hc34, hlam, hphi, p925_1, u3ehi1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h883, h924, hc34, hlam, hphi, p925_1, u3ehi1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h578, h924, hc02, hc34, hlam, hphi, ht23, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          rcases p925_3 (m.d 0 5) (by simp) with h947 | h947
                          · linarith only [h665, h947, hlam]
                          · linarith only [h876, h947, hlam]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h876, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h885, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h923, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h924, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                      · linarith only [h1, h876, h886, h924, hlam]
                    · linarith only [h1, h876, h923, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                · rcases m.htr 2 3 5 (by decide) (by decide) with h958 | h958
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h959 | h959
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h960 | h960
                      · linarith only [h879, h885, h960, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h1, h876, h879, h957, h960, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h876, h959, hlam]
                  · linarith only [h1, h876, h879, h885, h957, h958, hc35, hlam, hphi, u3ehi1]
                · linarith only [h1, h876, h879, h885, h957, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h966 | h966
        · linarith only [h0, h578, h966, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
          · rcases m.htr 1 3 5 (by decide) (by decide) with h969 | h969
            · linarith only [h665, h969, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h968, h969, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h972 | h972
            · linarith only [h968, h972, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h974 | h974
              · linarith only [h0, h876, h974, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h976 | h976
                · rcases m.htr 2 3 5 (by decide) (by decide) with h977 | h977
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h979 | h979
                      · linarith only [h1, h876, h976, h979, hc02, hc23, hlam, hphi]
                      · linarith only [h968, h979, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h968, h976, h978, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h968, h976, h977, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h984 | h984
                  · linarith only [h976, h984, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h986 | h986
                    · linarith only [h968, h974, h976, h986, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h988 | h988
                      · linarith only [h968, h974, h988, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h968, h988, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 3432000 in
theorem r1l7_11_13_25_L_0_L_R_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_0_L_R_H_I_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_0_L_R_H_I_x0_x1 m hb1 hb3 hb5 h0 h1

end R2N4
