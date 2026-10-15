import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h654 | h654
  · rcases m.htr 1 2 3 (by decide) (by decide) with h655 | h655
    · rcases m.htr 1 2 4 (by decide) (by decide) with h656 | h656
      · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
        · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
          · linarith only [h1, h5, h658, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h660 | h660
            · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
              · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                · linarith only [h0, h5, h655, h662, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
                  · linarith only [h0, h656, h664, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h2, h661, h662, h664, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h4, h654, h658, h660, h661, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
              · rcases m.htr 2 3 4 (by decide) (by decide) with h669 | h669
                · linarith only [h0, h5, h655, h669, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h671 | h671
                  · linarith only [h0, h656, h671, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h0, h656, h668, h671, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                · linarith only [h5, h654, h655, h658, h668, h674, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                  · linarith only [h0, h4, h655, h658, h668, h676, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h678 | h678
                    · rcases h1bigk with h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h657, hc25, hlam, hphi, ht01, ht0b, ht5b, p679_1, u1elo0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        rcases p679_3 (m.d 0 1) (by simp) with h682 | h682
                        · rcases p679_3 (m.d 1 2) (by simp) with h683 | h683
                          · linarith only [h0, h683, hlam]
                          · linarith only [h655, h683, hlam]
                        · linarith only [h682, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        rcases p679_3 (m.d 0 1) (by simp) with h687 | h687
                        · rcases p679_3 (m.d 1 2) (by simp) with h688 | h688
                          · linarith only [h0, h688, hlam]
                          · linarith only [h656, h688, hlam]
                        · linarith only [h687, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        rcases p679_3 (m.d 0 1) (by simp) with h692 | h692
                        · rcases p679_3 (m.d 1 2) (by simp) with h693 | h693
                          · linarith only [h0, h693, hlam]
                          · linarith only [h657, h693, hlam]
                        · linarith only [h692, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h0, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h0, h655, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p679_1, u1elo0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h0, h655, h658, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p679_1, u1elo0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p679_1, u1elo0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h1, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h655, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h658, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h660, hlam, p679_1]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h2, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h656, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h654, h655, h668, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p679_1]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h668, hlam, p679_1]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h3, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h657, hlam, p679_0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h3, h655, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p679_1, u1elo0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [h0, h4, h654, h668, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p679_1, u1elo0]
                      · have p679_0 := h679c.1
                        have p679_1 := h679c.2.1
                        have p679_2 := h679c.2.2.1
                        have p679_3 := h679c.2.2.2
                        linarith only [hlam, p679_0]
                    · linarith only [h0, h1, h4, h5, h654, h655, h678, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h718 | h718
          · linarith only [h1, h5, h654, h718, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h720 | h720
            · linarith only [h656, h657, h718, h720, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h722 | h722
              · linarith only [h656, h657, h722, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h724 | h724
                · linarith only [h5, h654, h655, h657, h722, h724, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h726 | h726
                  · linarith only [h0, h4, h718, h722, h726, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h5, h654, h656, h657, h724, h726, hc23, hc34, hlam, hphi]
      · linarith only [h0, h4, h655, h656, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h730 | h730
      · rcases m.htr 1 2 5 (by decide) (by decide) with h731 | h731
        · rcases m.htr 1 3 4 (by decide) (by decide) with h732 | h732
          · linarith only [h1, h5, h732, hlam]
          · linarith only [h655, h730, h732, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
          · linarith only [h1, h5, h654, h735, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · linarith only [h655, h730, h735, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h738 | h738
        · linarith only [h0, h4, h730, h738, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
          · linarith only [h1, h5, h740, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h742 | h742
            · rcases m.htr 1 4 5 (by decide) (by decide) with h743 | h743
              · rcases m.htr 2 3 4 (by decide) (by decide) with h744 | h744
                · linarith only [h0, h1, h4, h5, h742, h744, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                    · rcases h1bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        rcases p748_3 (m.d 0 1) (by simp) with h750 | h750
                        · rcases p748_3 (m.d 1 2) (by simp) with h751 | h751
                          · linarith only [h751, hlam, p748_0]
                          · rcases p748_3 (m.d 1 3) (by simp) with h753 | h753
                            · linarith only [h1, h753, hlam]
                            · linarith only [h655, h753, hlam]
                        · linarith only [h750, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h742, h747, hc45, hlam, hphi, ht01, ht0b, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h740, h742, h747, hc45, hlam, hphi, ht01, ht0b, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        rcases p748_3 (m.d 0 1) (by simp) with h759 | h759
                        · rcases p748_3 (m.d 1 2) (by simp) with h760 | h760
                          · linarith only [h0, h760, hlam]
                          · rcases p748_3 (m.d 1 3) (by simp) with h762 | h762
                            · linarith only [h1, h762, hlam]
                            · linarith only [h742, h762, hlam]
                        · linarith only [h759, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h655, hlam, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h730, hlam, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h738, hlam, p748_1]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h1, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h740, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, h4, h730, h740, hc15, hlam, hphi, ht01, ht0b, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h2, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, h4, h730, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, h4, h730, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h0, h4, h730, h738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h3, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p748_1, u1elo0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h742, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [h743, hlam, p748_0]
                      · have p748_0 := h748c.1
                        have p748_1 := h748c.2.1
                        have p748_2 := h748c.2.2.1
                        have p748_3 := h748c.2.2.2
                        linarith only [hlam, p748_0]
                    · linarith only [h2, h5, h654, h747, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h730, h743, h746, hlam]
              · linarith only [h0, h4, h654, h740, h742, h743, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h789 | h789
              · rcases m.htr 2 3 4 (by decide) (by decide) with h790 | h790
                · linarith only [h4, h5, h790, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h793 | h793
                    · rcases h1bigk with h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        rcases p794_3 (m.d 0 1) (by simp) with h796 | h796
                        · rcases p794_3 (m.d 1 2) (by simp) with h797 | h797
                          · linarith only [h797, hlam, p794_0]
                          · rcases p794_3 (m.d 1 3) (by simp) with h799 | h799
                            · linarith only [h1, h799, hlam]
                            · linarith only [h655, h799, hlam]
                        · linarith only [h796, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        rcases p794_3 (m.d 0 1) (by simp) with h803 | h803
                        · rcases p794_3 (m.d 1 2) (by simp) with h804 | h804
                          · linarith only [h0, h804, hlam]
                          · rcases p794_3 (m.d 1 3) (by simp) with h806 | h806
                            · linarith only [h806, hlam, p794_0]
                            · rcases p794_3 (m.d 1 4) (by simp) with h808 | h808
                              · linarith only [h2, h808, hlam]
                              · linarith only [h740, h808, hlam]
                        · linarith only [h803, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h789, hc45, hlam, hphi, ht01, ht0b, ht5b, p794_1, u1elo0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        rcases p794_3 (m.d 0 1) (by simp) with h813 | h813
                        · rcases p794_3 (m.d 1 2) (by simp) with h814 | h814
                          · linarith only [h0, h814, hlam]
                          · rcases p794_3 (m.d 1 3) (by simp) with h816 | h816
                            · linarith only [h1, h816, hlam]
                            · rcases p794_3 (m.d 1 4) (by simp) with h818 | h818
                              · linarith only [h2, h818, hlam]
                              · linarith only [h789, h818, hlam]
                        · linarith only [h813, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h0, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h655, hlam, p794_1]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h730, hlam, p794_1]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h738, hlam, p794_1]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h1, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h742, hc12, hc35, hlam, hphi, ht23, p794_1]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h740, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h742, hlam, p794_1]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h2, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p794_1, u1elo0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p794_1, u1elo0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h0, h4, h730, hc15, hlam, hphi, ht01, ht0b, ht5b, p794_1, u1elo0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h3, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p794_1, u1elo0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h3, h655, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p794_1, u1elo0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [h789, hlam, p794_0]
                      · have p794_0 := h794c.1
                        have p794_1 := h794c.2.1
                        have p794_2 := h794c.2.2.1
                        have p794_3 := h794c.2.2.2
                        linarith only [hlam, p794_0]
                    · linarith only [h5, h654, h793, hlam]
                  · linarith only [h730, h789, h792, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                · linarith only [h5, h654, h730, h789, h844, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h846 | h846
                  · linarith only [h0, h4, h655, h740, h789, h846, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h5, h654, h730, h846, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
    · rcases m.htr 1 2 4 (by decide) (by decide) with h850 | h850
      · rcases m.htr 1 2 5 (by decide) (by decide) with h851 | h851
        · rcases m.htr 1 3 4 (by decide) (by decide) with h852 | h852
          · linarith only [h1, h5, h852, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h854 | h854
            · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
              · linarith only [h0, h654, h850, h855, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h852, h854, h855, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h858 | h858
              · linarith only [h2, h654, h858, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h860 | h860
                · linarith only [h5, h849, h860, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h862 | h862
                  · linarith only [h0, h654, h850, h862, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h864 | h864
                    · rcases h1bigk with h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p865_1, u1elo0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        rcases p865_3 (m.d 0 1) (by simp) with h868 | h868
                        · rcases p865_3 (m.d 1 2) (by simp) with h869 | h869
                          · linarith only [h0, h869, hlam]
                          · linarith only [h849, h869, hlam]
                        · linarith only [h868, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        rcases p865_3 (m.d 0 1) (by simp) with h873 | h873
                        · rcases p865_3 (m.d 1 2) (by simp) with h874 | h874
                          · linarith only [h0, h874, hlam]
                          · linarith only [h850, h874, hlam]
                        · linarith only [h873, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        rcases p865_3 (m.d 0 1) (by simp) with h878 | h878
                        · rcases p865_3 (m.d 1 2) (by simp) with h879 | h879
                          · linarith only [h0, h879, hlam]
                          · linarith only [h851, h879, hlam]
                        · linarith only [h878, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h0, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h0, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p865_1, u1elo0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h0, h849, h852, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p865_1, u1elo0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h0, h849, h852, h858, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p865_1, u1elo0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h1, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h849, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h852, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h854, hlam, p865_1]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h2, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h850, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h2, h654, h849, h864, hc23, hc34, hlam, hphi, p865_1]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h858, hlam, p865_1]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h3, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h851, hlam, p865_0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h3, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p865_1, u1elo0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [h0, h851, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p865_1, u1elo0]
                      · have p865_0 := h865c.1
                        have p865_1 := h865c.2.1
                        have p865_2 := h865c.2.2.1
                        have p865_3 := h865c.2.2.2
                        linarith only [hlam, p865_0]
                    · rcases h1bigk with h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h851, h862, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        rcases p903_3 (m.d 0 1) (by simp) with h906 | h906
                        · rcases p903_3 (m.d 1 2) (by simp) with h907 | h907
                          · linarith only [h0, h907, hlam]
                          · linarith only [h849, h907, hlam]
                        · linarith only [h906, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        rcases p903_3 (m.d 0 1) (by simp) with h911 | h911
                        · rcases p903_3 (m.d 1 2) (by simp) with h912 | h912
                          · linarith only [h0, h912, hlam]
                          · linarith only [h850, h912, hlam]
                        · linarith only [h911, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        rcases p903_3 (m.d 0 1) (by simp) with h916 | h916
                        · rcases p903_3 (m.d 1 2) (by simp) with h917 | h917
                          · linarith only [h0, h917, hlam]
                          · linarith only [h851, h917, hlam]
                        · linarith only [h916, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h0, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h0, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h0, h849, h852, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h1, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h849, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h852, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h854, hlam, p903_1]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h2, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h850, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h2, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h858, hlam, p903_1]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h3, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h851, hlam, p903_0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h3, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [h0, h851, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p903_1, u1elo0]
                      · have p903_0 := h903c.1
                        have p903_1 := h903c.2.1
                        have p903_2 := h903c.2.2.1
                        have p903_3 := h903c.2.2.2
                        linarith only [hlam, p903_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h941 | h941
          · linarith only [h1, h5, h941, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
            · linarith only [h849, h851, h943, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h945 | h945
              · linarith only [h0, h654, h850, h945, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h947 | h947
                · linarith only [h3, h5, h849, h851, h947, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h949 | h949
                  · linarith only [h3, h654, h850, h851, h949, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h951 | h951
                    · linarith only [h849, h851, h949, h951, hc23, hc34, hlam, hphi]
                    · rcases h1bigk with h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h850, h947, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        rcases p953_3 (m.d 0 1) (by simp) with h956 | h956
                        · rcases p953_3 (m.d 1 2) (by simp) with h957 | h957
                          · linarith only [h0, h957, hlam]
                          · linarith only [h849, h957, hlam]
                        · linarith only [h956, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        rcases p953_3 (m.d 0 1) (by simp) with h961 | h961
                        · rcases p953_3 (m.d 1 2) (by simp) with h962 | h962
                          · linarith only [h0, h962, hlam]
                          · linarith only [h850, h962, hlam]
                        · linarith only [h961, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h850, h851, h947, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h0, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h0, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h851, hlam, p953_1]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h1, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h849, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h941, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h943, hlam, p953_1]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h2, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h850, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h2, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h945, hlam, p953_1]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h3, hlam, p953_0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h3, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p953_1, u1elo0]
                      · have p953_0 := h953c.1
                        have p953_1 := h953c.2.1
                        have p953_2 := h953c.2.2.1
                        have p953_3 := h953c.2.2.2
                        linarith only [hlam, p953_0]
      · linarith only [h0, h4, h849, h850, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h988 | h988
      · rcases m.htr 1 2 5 (by decide) (by decide) with h989 | h989
        · rcases m.htr 1 3 4 (by decide) (by decide) with h990 | h990
          · linarith only [h1, h5, h990, hlam]
          · linarith only [h849, h988, h990, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
          · linarith only [h1, h5, h993, hlam]
          · linarith only [h849, h988, h993, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h996 | h996
        · linarith only [h0, h4, h988, h996, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h998 | h998
          · linarith only [h1, h5, h998, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1000 | h1000
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1001 | h1001
              · linarith only [h0, h1001, h4, h654, h988, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1000, h1001, h998, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1004 | h1004
              · linarith only [h1004, h4, h654, h988, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1006 | h1006
                · linarith only [h1006, h4, h5, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1008 | h1008
                  · linarith only [h1008, h4, h654, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                    · linarith only [h1010, h4, h654, h988, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1006, h1010, h849, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x0_x0 m hb1 hb4 hg0 h1 h2 h3 h4 h5
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x0_x1 m hb1 hb4 hg0 h1 h2 h3 h4 h5

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1013 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h1014 | h1014
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1015 | h1015
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1016 | h1016
      · linarith only [h0, h1016, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1018 | h1018
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1019 | h1019
          · linarith only [h1015, h1016, h1019, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1021 | h1021
            · linarith only [h1, h1013, h1019, h1021, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1023 | h1023
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1024 | h1024
                · linarith only [h1015, h1016, h1019, h1024, hlam]
                · linarith only [h0, h1, h1013, h1015, h1024, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1, h1013, h1014, h1015, h1016, h1023, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1028 | h1028
          · linarith only [h1015, h1016, h1028, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1030 | h1030
            · linarith only [h1, h1013, h1028, h1030, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1033 | h1033
                · linarith only [h1015, h1028, h1033, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h1013, h1033, h4, hlam]
              · linarith only [h1014, h1015, h1016, h1032, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1037 | h1037
      · linarith only [h0, h1014, h1037, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1039 | h1039
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1040 | h1040
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1041 | h1041
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1042 | h1042
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1043 | h1043
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1044 | h1044
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1045 | h1045
                    · linarith only [h1, h1040, h1045, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h1, h1037, h1039, h1040, h1044, h1045, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h1014, h1039, h1044, h4, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h1, h1013, h1015, h1039, h1043, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h1013, h1014, h1037, h1039, h1042, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1037, h1039, h1040, h1041, hlam]
          · linarith only [h1, h1013, h1015, h1039, h1040, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1054 | h1054
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1055 | h1055
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1056 | h1056
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1057 | h1057
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1058 | h1058
                    · linarith only [h1, h1053, h1058, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h1055, h1058, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h1053, h1055, h1057, h4, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h1013, h1015, h1056, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1064 | h1064
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1065 | h1065
                    · linarith only [h1053, h1055, h1065, hlam]
                    · rcases h1bigk with h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c | h1067c
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        rcases p1067_3 (m.d 0 1) (by simp) with h1069 | h1069
                        · rcases p1067_3 (m.d 1 2) (by simp) with h1070 | h1070
                          · linarith only [h1070, hlam, p1067_0]
                          · rcases p1067_3 (m.d 1 3) (by simp) with h1072 | h1072
                            · linarith only [h1, h1072, hlam]
                            · linarith only [h1015, h1072, hlam]
                        · linarith only [h1069, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1053, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1067_1, u1elo0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        rcases p1067_3 (m.d 0 1) (by simp) with h1077 | h1077
                        · rcases p1067_3 (m.d 1 2) (by simp) with h1078 | h1078
                          · linarith only [h0, h1078, hlam]
                          · rcases p1067_3 (m.d 1 3) (by simp) with h1080 | h1080
                            · linarith only [h1, h1080, hlam]
                            · linarith only [h1053, h1080, hlam]
                        · linarith only [h1077, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        rcases p1067_3 (m.d 0 1) (by simp) with h1084 | h1084
                        · rcases p1067_3 (m.d 1 2) (by simp) with h1085 | h1085
                          · linarith only [h0, h1085, hlam]
                          · rcases p1067_3 (m.d 1 3) (by simp) with h1087 | h1087
                            · linarith only [h1, h1087, hlam]
                            · linarith only [h1054, h1087, hlam]
                        · linarith only [h1084, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h0, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1015, hlam, p1067_1]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1037, hlam, p1067_1]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1039, hlam, p1067_1]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1067_1, u1elo0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1, h1037, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1067_1, u1elo0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1, h1037, h1055, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1067_1, u1elo0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h2, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1014, h1055, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1067_1]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1053, hlam, p1067_1]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1055, hlam, p1067_1]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h3, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1067_1, u1elo0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1054, hlam, p1067_0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [h1, h1013, h1014, h1055, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1067_1, u1elo0]
                      · have p1067_0 := h1067c.1
                        have p1067_1 := h1067c.2.1
                        have p1067_2 := h1067c.2.2.1
                        have p1067_3 := h1067c.2.2.2
                        linarith only [hlam, p1067_0]
                  · linarith only [h0, h1, h1013, h1014, h1064, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h1, h1013, h1015, h1063, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1113 | h1113
              · linarith only [h1053, h1054, h1113, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1115 | h1115
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1117 | h1117
                    · linarith only [h1053, h1054, h1113, h1117, hlam]
                    · linarith only [h1, h1013, h1014, h1053, h1054, h1117, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1014, h1116, h4, hlam]
                · linarith only [h1053, h1054, h1115, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1122 | h1122
            · linarith only [h1, h1013, h1053, h1122, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1124 | h1124
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1125 | h1125
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1126 | h1126
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1127 | h1127
                    · rcases h1bigk with h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        rcases p1128_3 (m.d 0 1) (by simp) with h1130 | h1130
                        · rcases p1128_3 (m.d 1 2) (by simp) with h1131 | h1131
                          · linarith only [h1131, hlam, p1128_0]
                          · rcases p1128_3 (m.d 1 3) (by simp) with h1133 | h1133
                            · linarith only [h1, h1133, hlam]
                            · linarith only [h1015, h1133, hlam]
                        · linarith only [h1130, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        rcases p1128_3 (m.d 0 1) (by simp) with h1137 | h1137
                        · rcases p1128_3 (m.d 1 2) (by simp) with h1138 | h1138
                          · linarith only [h0, h1138, hlam]
                          · rcases p1128_3 (m.d 1 3) (by simp) with h1140 | h1140
                            · linarith only [h1140, hlam, p1128_0]
                            · rcases p1128_3 (m.d 1 4) (by simp) with h1142 | h1142
                              · linarith only [h1142, h2, hlam]
                              · linarith only [h1053, h1142, hlam]
                        · linarith only [h1137, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1124, hc45, hlam, hphi, ht01, ht0b, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        rcases p1128_3 (m.d 0 1) (by simp) with h1147 | h1147
                        · rcases p1128_3 (m.d 1 2) (by simp) with h1148 | h1148
                          · linarith only [h0, h1148, hlam]
                          · rcases p1128_3 (m.d 1 3) (by simp) with h1150 | h1150
                            · linarith only [h1, h1150, hlam]
                            · rcases p1128_3 (m.d 1 4) (by simp) with h1152 | h1152
                              · linarith only [h1152, h2, hlam]
                              · linarith only [h1124, h1152, hlam]
                        · linarith only [h1147, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h0, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1015, hlam, p1128_1]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1037, hlam, p1128_1]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1039, hlam, p1128_1]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1, h1013, h1122, h1127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1053, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1122, hlam, p1128_1]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h2, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1, h1013, h1053, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1, h1013, h1053, hc15, hlam, hphi, ht01, ht0b, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h3, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1, h1013, h1015, h1122, h1127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1128_1, u1elo0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [h1124, hlam, p1128_0]
                      · have p1128_0 := h1128c.1
                        have p1128_1 := h1128c.2.1
                        have p1128_2 := h1128c.2.2.1
                        have p1128_3 := h1128c.2.2.2
                        linarith only [hlam, p1128_0]
                    · linarith only [h1, h1013, h1014, h1015, h1053, h1127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1014, h1126, h4, hlam]
                · linarith only [h1, h1013, h1015, h1125, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1179 | h1179
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1180 | h1180
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1181 | h1181
                    · linarith only [h1, h1013, h1015, h1053, h1124, h1181, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1014, h1015, h1053, h1181, h4, hc12, hc24, hlam, hphi]
                  · linarith only [h1014, h1180, h4, hlam]
                · linarith only [h1, h1013, h1015, h1179, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1186 | h1186
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1187 | h1187
      · linarith only [h0, h1187, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1189 | h1189
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1190 | h1190
          · linarith only [h1186, h1187, h1190, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1192 | h1192
            · linarith only [h1, h1013, h1190, h1192, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1194 | h1194
              · linarith only [h1014, h1194, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1187, h1189, h1194, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1197 | h1197
          · linarith only [h1186, h1187, h1197, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1199 | h1199
            · linarith only [h1, h1013, h1197, h1199, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1201 | h1201
              · linarith only [h1013, h1014, h1197, h1201, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1203 | h1203
                · linarith only [h1186, h1187, h1197, h1203, hlam]
                · linarith only [h0, h1013, h1014, h1186, h1203, h4, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1206 | h1206
      · linarith only [h0, h1206, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1209 | h1209
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1210 | h1210
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1211 | h1211
              · linarith only [h1, h1014, h1209, h1211, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1206, h1208, h1211, hlam]
            · linarith only [h1186, h1208, h1210, hlam]
          · linarith only [h1, h1013, h1186, h1208, h1209, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1216 | h1216
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1217 | h1217
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1218 | h1218
              · linarith only [h1014, h1218, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1220 | h1220
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1221 | h1221
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1222 | h1222
                    · linarith only [h1014, h1216, h1222, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases h1bigk with h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        rcases p1224_3 (m.d 0 1) (by simp) with h1226 | h1226
                        · rcases p1224_3 (m.d 1 2) (by simp) with h1227 | h1227
                          · linarith only [h1227, hlam, p1224_0]
                          · rcases p1224_3 (m.d 1 3) (by simp) with h1229 | h1229
                            · linarith only [h1, h1229, hlam]
                            · linarith only [h1186, h1229, hlam]
                        · linarith only [h1226, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1217, hc35, hlam, hphi, ht01, ht0b, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        rcases p1224_3 (m.d 0 1) (by simp) with h1234 | h1234
                        · rcases p1224_3 (m.d 1 2) (by simp) with h1235 | h1235
                          · linarith only [h0, h1235, hlam]
                          · rcases p1224_3 (m.d 1 3) (by simp) with h1237 | h1237
                            · linarith only [h1, h1237, hlam]
                            · linarith only [h1216, h1237, hlam]
                        · linarith only [h1234, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        rcases p1224_3 (m.d 0 1) (by simp) with h1241 | h1241
                        · rcases p1224_3 (m.d 1 2) (by simp) with h1242 | h1242
                          · linarith only [h0, h1242, hlam]
                          · rcases p1224_3 (m.d 1 3) (by simp) with h1244 | h1244
                            · linarith only [h1, h1244, hlam]
                            · linarith only [h1217, h1244, hlam]
                        · linarith only [h1241, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h0, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1186, hlam, p1224_1]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1206, hlam, p1224_1]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1208, hlam, p1224_1]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1, h1206, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h2, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1216, hlam, p1224_1]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1218, hlam, p1224_1]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h3, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h1217, hlam, p1224_0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1224_1, u1elo0]
                      · have p1224_0 := h1224c.1
                        have p1224_1 := h1224c.2.1
                        have p1224_2 := h1224c.2.2.1
                        have p1224_3 := h1224c.2.2.2
                        linarith only [hlam, p1224_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1268 | h1268
                    · linarith only [h0, h1221, h1268, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        rcases p1270_3 (m.d 0 1) (by simp) with h1272 | h1272
                        · rcases p1270_3 (m.d 1 2) (by simp) with h1273 | h1273
                          · linarith only [h1273, hlam, p1270_0]
                          · rcases p1270_3 (m.d 1 3) (by simp) with h1275 | h1275
                            · linarith only [h1, h1275, hlam]
                            · linarith only [h1186, h1275, hlam]
                        · linarith only [h1272, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1217, h1268, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        rcases p1270_3 (m.d 0 1) (by simp) with h1280 | h1280
                        · rcases p1270_3 (m.d 1 2) (by simp) with h1281 | h1281
                          · linarith only [h0, h1281, hlam]
                          · rcases p1270_3 (m.d 1 3) (by simp) with h1283 | h1283
                            · linarith only [h1, h1283, hlam]
                            · linarith only [h1216, h1283, hlam]
                        · linarith only [h1280, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        rcases p1270_3 (m.d 0 1) (by simp) with h1287 | h1287
                        · rcases p1270_3 (m.d 1 2) (by simp) with h1288 | h1288
                          · linarith only [h0, h1288, hlam]
                          · rcases p1270_3 (m.d 1 3) (by simp) with h1290 | h1290
                            · linarith only [h1, h1290, hlam]
                            · linarith only [h1217, h1290, hlam]
                        · linarith only [h1287, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h0, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1186, hlam, p1270_1]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1206, hlam, p1270_1]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1208, hlam, p1270_1]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1, h1206, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h2, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1216, hlam, p1270_1]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1218, hlam, p1270_1]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h3, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1217, hlam, p1270_0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [h1, h1217, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1270_1, u1elo0]
                      · have p1270_0 := h1270c.1
                        have p1270_1 := h1270c.2.1
                        have p1270_2 := h1270c.2.2.1
                        have p1270_3 := h1270c.2.2.2
                        linarith only [hlam, p1270_0]
                · linarith only [h1, h1013, h1186, h1220, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1315 | h1315
              · linarith only [h1014, h1315, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1318 | h1318
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1319 | h1319
                    · linarith only [h1014, h1216, h1319, h2, hlam]
                    · rcases h1bigk with h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c | h1321c
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        rcases p1321_3 (m.d 0 1) (by simp) with h1323 | h1323
                        · rcases p1321_3 (m.d 1 2) (by simp) with h1324 | h1324
                          · linarith only [h1324, hlam, p1321_0]
                          · rcases p1321_3 (m.d 1 3) (by simp) with h1326 | h1326
                            · linarith only [h1, h1326, hlam]
                            · linarith only [h1186, h1326, hlam]
                        · linarith only [h1323, hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1216, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1321_1, u1elo0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        rcases p1321_3 (m.d 0 1) (by simp) with h1331 | h1331
                        · rcases p1321_3 (m.d 1 2) (by simp) with h1332 | h1332
                          · linarith only [h0, h1332, hlam]
                          · rcases p1321_3 (m.d 1 3) (by simp) with h1334 | h1334
                            · linarith only [h1, h1334, hlam]
                            · linarith only [h1216, h1334, hlam]
                        · linarith only [h1331, hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1216, h1217, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1321_1, u1elo0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h0, hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1186, hlam, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1206, hlam, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1208, hlam, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1, hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1217, h1317, h1318, h1319, hc12, hc23, hlam, hphi, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1217, h1317, h1318, h1319, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1217, hlam, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h2, hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1321_1, u1elo0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1216, hlam, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1315, hlam, p1321_1]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h3, hlam, p1321_0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1216, h1217, h1317, h1318, h1319, h3, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1321_1, u1elo0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h1216, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1321_1, u1elo0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1321_1, u1elo0]
                      · have p1321_0 := h1321c.1
                        have p1321_1 := h1321c.2.1
                        have p1321_2 := h1321c.2.2.1
                        have p1321_3 := h1321c.2.2.2
                        linarith only [hlam, p1321_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1359 | h1359
                    · linarith only [h1216, h1318, h1359, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases h1bigk with h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        rcases p1361_3 (m.d 0 1) (by simp) with h1363 | h1363
                        · rcases p1361_3 (m.d 1 2) (by simp) with h1364 | h1364
                          · linarith only [h1364, hlam, p1361_0]
                          · rcases p1361_3 (m.d 1 3) (by simp) with h1366 | h1366
                            · linarith only [h1, h1366, hlam]
                            · linarith only [h1186, h1366, hlam]
                        · linarith only [h1363, hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1216, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        rcases p1361_3 (m.d 0 1) (by simp) with h1371 | h1371
                        · rcases p1361_3 (m.d 1 2) (by simp) with h1372 | h1372
                          · linarith only [h0, h1372, hlam]
                          · rcases p1361_3 (m.d 1 3) (by simp) with h1374 | h1374
                            · linarith only [h1, h1374, hlam]
                            · linarith only [h1216, h1374, hlam]
                        · linarith only [h1371, hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1216, h1217, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h0, hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1186, hlam, p1361_1]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1206, hlam, p1361_1]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1208, hlam, p1361_1]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1, hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1217, hlam, p1361_1]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h2, hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1216, hlam, p1361_1]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h1315, hlam, p1361_1]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h3, hlam, p1361_0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u1elo0]
                      · have p1361_0 := h1361c.1
                        have p1361_1 := h1361c.2.1
                        have p1361_2 := h1361c.2.2.1
                        have p1361_3 := h1361c.2.2.2
                        linarith only [hlam, p1361_0]
                · linarith only [h1, h1216, h1317, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1400 | h1400
            · linarith only [h1, h1013, h1216, h1400, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1402 | h1402
              · linarith only [h1014, h1402, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1404 | h1404
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1405 | h1405
                  · linarith only [h1013, h1014, h1186, h1216, h1405, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1407 | h1407
                    · linarith only [h1, h1013, h1405, h1407, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases h1bigk with h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 1) (by simp) with h1411 | h1411
                        · rcases p1409_3 (m.d 1 2) (by simp) with h1412 | h1412
                          · linarith only [h1412, hlam, p1409_0]
                          · rcases p1409_3 (m.d 1 3) (by simp) with h1414 | h1414
                            · linarith only [h1, h1414, hlam]
                            · linarith only [h1186, h1414, hlam]
                        · linarith only [h1411, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 1) (by simp) with h1418 | h1418
                        · rcases p1409_3 (m.d 1 2) (by simp) with h1419 | h1419
                          · linarith only [h0, h1419, hlam]
                          · rcases p1409_3 (m.d 1 3) (by simp) with h1421 | h1421
                            · linarith only [h1421, hlam, p1409_0]
                            · rcases p1409_3 (m.d 1 4) (by simp) with h1423 | h1423
                              · linarith only [h1423, h2, hlam]
                              · linarith only [h1216, h1423, hlam]
                        · linarith only [h1418, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 1) (by simp) with h1427 | h1427
                        · rcases p1409_3 (m.d 1 2) (by simp) with h1428 | h1428
                          · linarith only [h0, h1428, hlam]
                          · rcases p1409_3 (m.d 1 3) (by simp) with h1430 | h1430
                            · linarith only [h1, h1430, hlam]
                            · rcases p1409_3 (m.d 1 4) (by simp) with h1432 | h1432
                              · linarith only [h1432, hlam, p1409_0]
                              · rcases p1409_3 (m.d 1 5) (by simp) with h1434 | h1434
                                · linarith only [h1434, h3, hlam]
                                · linarith only [h1402, h1434, hlam]
                        · linarith only [h1427, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 1) (by simp) with h1438 | h1438
                        · rcases p1409_3 (m.d 1 2) (by simp) with h1439 | h1439
                          · linarith only [h0, h1439, hlam]
                          · rcases p1409_3 (m.d 1 3) (by simp) with h1441 | h1441
                            · linarith only [h1, h1441, hlam]
                            · rcases p1409_3 (m.d 1 4) (by simp) with h1443 | h1443
                              · linarith only [h1443, h2, hlam]
                              · rcases p1409_3 (m.d 1 5) (by simp) with h1445 | h1445
                                · linarith only [h1445, hlam, p1409_0]
                                · rcases h4bigk with h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c | h1447c
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1186, h1216, h1405, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h4, hlam, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1405, h4, hc34, hc45, hlam, hphi, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1014, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h2, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1206, hlam, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1216, hlam, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1402, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1405, hc04, hc45, hlam, hphi, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1186, h1216, h1405, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1186, h1216, h1405, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1405, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1013, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1013, h1186, h1216, h1405, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1404, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1407, hlam, p1447_0]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1013, h1186, h1216, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    rcases p1447_3 (m.d 0 4) (by simp) with h1469 | h1469
                                    · linarith only [h1014, h1469, hlam]
                                    · linarith only [h1469, h2, hlam]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [h1186, h1216, hc12, hc45, hlam, hphi, ht23, ht34, p1447_1]
                                  · have p1447_0 := h1447c.1
                                    have p1447_1 := h1447c.2.1
                                    have p1447_2 := h1447c.2.2.1
                                    have p1447_3 := h1447c.2.2.2
                                    linarith only [hlam, p1447_0]
                        · linarith only [h1438, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h0, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1186, hlam, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1206, hlam, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1208, hlam, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1013, h1216, h4, hc12, hc24, hlam, hphi, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1216, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1400, hlam, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h2, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1402, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1409_1, u1elo0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1402, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1409_1, u1elo0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1402, hlam, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h3, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1409_1, u1elo0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1186, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1409_1, u1elo0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1409_1, u1elo0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                · linarith only [h1, h1013, h1186, h1404, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]

end R2N4
