import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_64S9

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_15_M_LI_L_R_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h668 | h668
  · rcases m.htr 0 1 4 (by decide) (by decide) with h669 | h669
    · rcases m.htr 0 1 5 (by decide) (by decide) with h670 | h670
      · linarith only [h0, h670, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h672 | h672
        · rcases m.htr 1 2 3 (by decide) (by decide) with h673 | h673
          · rcases m.htr 1 2 4 (by decide) (by decide) with h674 | h674
            · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
              · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
                · linarith only [h668, h670, h675, h676, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                  · linarith only [h669, h670, h675, h676, h678, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
                    · linarith only [h669, h670, h675, h680, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h682 | h682
                      · linarith only [h673, h676, h682, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h684 | h684
                        · linarith only [h669, h670, h673, h676, h678, h684, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h686 | h686
                          · linarith only [h669, h670, h676, h680, h686, hc13, hc34, hlam, hphi]
                          · rcases h1bigk with h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h0, hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h670, h673, h675, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p688_1, u1elo1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h670, h673, h675, h676, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p688_1, u1elo1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h670, hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hc01, hlam, hphi, p688_1, u1elo1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              rcases p688_3 (m.d 0 1) (by simp) with h696 | h696
                              · linarith only [h0, h696, hlam]
                              · linarith only [h668, h696, hlam]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              rcases p688_3 (m.d 0 1) (by simp) with h699 | h699
                              · linarith only [h0, h699, hlam]
                              · linarith only [h669, h699, hlam]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p688_1, u1elo1, u5ehi1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h668, hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h673, hlam, p688_1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h676, hlam, p688_1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h678, hlam, p688_1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h669, hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h674, hlam, p688_1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h669, h673, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p688_1, u1elo0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hlam, p688_0]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h680, hlam, p688_1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hc01, hlam, hphi, p688_1, u1elo4]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [h675, hlam, p688_1]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              rcases p688_3 (m.d 0 1) (by simp) with h715 | h715
                              · linarith only [h670, h715, hlam]
                              · linarith only [h668, h715, hlam]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              rcases p688_3 (m.d 0 1) (by simp) with h718 | h718
                              · linarith only [h670, h718, hlam]
                              · linarith only [h669, h718, hlam]
                            · have p688_0 := h688c.1
                              have p688_1 := h688c.2.1
                              have p688_2 := h688c.2.2.1
                              have p688_3 := h688c.2.2.2
                              linarith only [hlam, p688_0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
                · linarith only [h0, h668, h675, h722, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h724 | h724
                  · linarith only [h0, h669, h675, h722, h724, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h726 | h726
                    · linarith only [h0, h669, h675, h726, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h728 | h728
                      · linarith only [h673, h722, h728, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h730 | h730
                        · linarith only [h0, h669, h673, h675, h722, h724, h730, hlam]
                        · linarith only [h0, h669, h673, h675, h722, h730, hc23, hc35, hlam, hphi]
            · linarith only [h0, h669, h674, hlam]
          · linarith only [h0, h669, h672, h673, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h668, h672, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h736 | h736
      · linarith only [h669, h736, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h738 | h738
        · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
          · rcases m.htr 1 2 4 (by decide) (by decide) with h740 | h740
            · rcases m.htr 1 2 5 (by decide) (by decide) with h741 | h741
              · rcases m.htr 1 3 4 (by decide) (by decide) with h742 | h742
                · linarith only [h668, h669, h740, h742, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h744 | h744
                  · linarith only [h668, h669, h740, h744, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h746 | h746
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h747 | h747
                      · linarith only [h668, h736, h739, h742, h746, h747, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h749 | h749
                        · linarith only [h668, h736, h739, h744, h749, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h751 | h751
                          · rcases h1bigk with h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c | h752c
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h0, hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h736, h740, h746, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p752_1, u1elo1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h669, hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h736, hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [hc01, hlam, hphi, p752_1, u1elo1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              rcases p752_3 (m.d 0 1) (by simp) with h760 | h760
                              · linarith only [h0, h760, hlam]
                              · linarith only [h668, h760, hlam]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h746, hlam, hphi, ht01, ht0b, ht5b, p752_1, u1elo1, u5ehi1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h668, h736, h739, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p752_1, u1elo1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h668, hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h739, hlam, p752_1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h742, hlam, p752_1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h744, hlam, p752_1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h668, h739, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p752_1, u1elo3]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h740, hlam, p752_1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              rcases p752_3 (m.d 0 1) (by simp) with h772 | h772
                              · linarith only [h669, h772, hlam]
                              · linarith only [h668, h772, hlam]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h668, h736, h739, h740, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p752_1, u1elo1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h668, h739, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p752_1, u1elo4]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h741, hlam, p752_1]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              rcases p752_3 (m.d 0 1) (by simp) with h779 | h779
                              · linarith only [h736, h779, hlam]
                              · linarith only [h668, h779, hlam]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [h746, hlam, p752_0]
                            · have p752_0 := h752c.1
                              have p752_1 := h752c.2.1
                              have p752_2 := h752c.2.2.1
                              have p752_3 := h752c.2.2.2
                              linarith only [hlam, p752_0]
                          · linarith only [h668, h669, h739, h742, h751, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h668, h669, h739, h746, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                · linarith only [h668, h669, h786, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h788 | h788
                  · linarith only [h668, h669, h740, h741, h788, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h790 | h790
                    · linarith only [h740, h741, h790, hlam]
                    · linarith only [h668, h669, h790, hc13, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h793 | h793
              · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
                · linarith only [h0, h668, h740, h794, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
                  · linarith only [h668, h736, h740, h793, h796, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                      · linarith only [h668, h736, h739, h740, h793, h794, h799, hlam]
                      · linarith only [h668, h736, h739, h740, h793, h799, hc23, hc34, hlam, hphi]
                    · linarith only [h668, h736, h739, h740, h793, h798, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                · linarith only [h0, h668, h740, h803, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                  · linarith only [h0, h668, h740, h805, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h807 | h807
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h808 | h808
                      · linarith only [h0, h668, h739, h793, h803, h807, h808, hlam]
                      · linarith only [h0, h668, h739, h740, h808, hc23, hc34, hlam, hphi]
                    · linarith only [h668, h669, h739, h807, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h0, h668, h738, h739, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h668, h738, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h814 | h814
    · rcases m.htr 0 1 5 (by decide) (by decide) with h815 | h815
      · linarith only [h0, h815, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h817 | h817
        · rcases m.htr 1 2 3 (by decide) (by decide) with h818 | h818
          · rcases m.htr 1 2 4 (by decide) (by decide) with h819 | h819
            · rcases m.htr 1 2 5 (by decide) (by decide) with h820 | h820
              · rcases m.htr 1 3 4 (by decide) (by decide) with h821 | h821
                · rcases m.htr 1 3 5 (by decide) (by decide) with h822 | h822
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h823 | h823
                    · linarith only [h814, h815, h818, h822, h823, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h825 | h825
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h826 | h826
                        · linarith only [h0, h817, h826, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · linarith only [h818, h822, h825, h826, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h814, h815, h818, h821, h822, h825, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h830 | h830
                    · linarith only [h814, h830, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h832 | h832
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
                        · linarith only [h668, h822, h833, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h835 | h835
                          · linarith only [h668, h814, h819, h822, h830, h832, h835, hlam]
                          · linarith only [h668, h814, h819, h822, h832, h835, hc34, hc45, hlam, hphi]
                      · linarith only [h821, h822, h832, hc23, hc35, hlam, hphi]
                · linarith only [h668, h814, h821, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                  · linarith only [h818, h820, h841, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                    · linarith only [h668, h814, h841, h843, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h845 | h845
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
                        · linarith only [h668, h841, h846, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h848 | h848
                          · linarith only [h668, h814, h818, h819, h820, h843, h845, h848, hlam]
                          · linarith only [h668, h814, h818, h819, h820, h845, h846, h848, hc34, hc45, hlam, hphi]
                      · linarith only [h668, h814, h818, h840, h845, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h668, h814, h840, hlam]
            · linarith only [h668, h814, h818, h819, hlam]
          · linarith only [h0, h817, h818, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h855 | h855
          · linarith only [h0, h817, h855, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h857 | h857
            · rcases m.htr 1 2 5 (by decide) (by decide) with h858 | h858
              · rcases m.htr 1 3 4 (by decide) (by decide) with h859 | h859
                · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                    · linarith only [h814, h815, h858, h861, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h863 | h863
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h864 | h864
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h865 | h865
                          · linarith only [h814, h815, h857, h861, h863, h865, hlam]
                          · rcases h1bigk with h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h668, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h815, h855, h858, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p867_1, u1elo2]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h815, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h855, hc01, hlam, hphi, p867_1, u1elo2]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h855, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 1) (by simp) with h876 | h876
                              · linarith only [h0, h876, hlam]
                              · linarith only [h814, h876, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h855, hlam, hphi, ht01, ht0b, ht5b, p867_1, u1elo2, u5ehi1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h814, h857, h863, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p867_1, u1elo2]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h858, hlam, hphi, ht01, ht0b, ht5b, p867_1, u1elo2, u5ehi2]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 1) (by simp) with h883 | h883
                              · linarith only [h668, h883, hlam]
                              · linarith only [h814, h883, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h814, h815, h857, h863, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p867_1, u1elo2]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h814, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h857, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h859, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h861, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h814, h855, h857, h858, h863, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h858, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h860, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 1) (by simp) with h895 | h895
                              · linarith only [h815, h895, hlam]
                              · linarith only [h814, h895, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                        · linarith only [h0, h814, h855, h857, h863, h864, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h814, h815, h855, h857, h858, h863, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h855, h858, h860, hlam]
                · linarith only [h0, h814, h855, h859, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                · rcases m.htr 1 3 5 (by decide) (by decide) with h904 | h904
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h905 | h905
                    · linarith only [h0, h814, h858, h904, h905, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h907 | h907
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h908 | h908
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h909 | h909
                          · linarith only [h0, h814, h857, h858, h905, h907, h909, hlam]
                          · rcases h1bigk with h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c | h911c
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h0, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h668, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h0, h857, h858, h904, h907, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p911_1, u1elo2]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h815, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h858, h904, hc01, hlam, hphi, p911_1, u1elo2]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h855, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              rcases p911_3 (m.d 0 1) (by simp) with h920 | h920
                              · linarith only [h0, h920, hlam]
                              · linarith only [h814, h920, hlam]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h858, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h814, h857, h907, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p911_1, u1elo2]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h0, h814, h857, h907, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p911_1, u1elo2]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              rcases p911_3 (m.d 0 1) (by simp) with h927 | h927
                              · linarith only [h668, h927, hlam]
                              · linarith only [h814, h927, hlam]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p911_1, u1elo2, u5ehi1]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h814, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h857, hlam, p911_1]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h903, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h905, hlam, p911_1]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h814, h857, h907, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p911_1, u1elo4]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h0, h814, h857, h907, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p911_1, u1elo4]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [h904, hlam, p911_0]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              rcases p911_3 (m.d 0 1) (by simp) with h939 | h939
                              · linarith only [h815, h939, hlam]
                              · linarith only [h814, h939, hlam]
                            · have p911_0 := h911c.1
                              have p911_1 := h911c.2.1
                              have p911_2 := h911c.2.2.1
                              have p911_3 := h911c.2.2.2
                              linarith only [hlam, p911_0]
                        · linarith only [h0, h814, h817, h857, h904, h907, h908, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h814, h855, h857, h907, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h945 | h945
                    · linarith only [h0, h814, h945, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h947 | h947
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h948 | h948
                        · linarith only [h0, h814, h855, h857, h904, h947, h948, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h814, h855, h857, h947, h948, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h814, h855, h857, h947, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h814, h855, h903, hlam]
            · linarith only [h0, h814, h857, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h954 | h954
      · linarith only [h0, h954, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h956 | h956
        · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
          · rcases m.htr 1 2 4 (by decide) (by decide) with h958 | h958
            · rcases m.htr 1 2 5 (by decide) (by decide) with h959 | h959
              · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                · rcases m.htr 1 3 5 (by decide) (by decide) with h961 | h961
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h962 | h962
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h963 | h963
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
                        · linarith only [h0, h956, h964, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · linarith only [h957, h961, h963, h964, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h967 | h967
                        · linarith only [h0, h956, h967, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h969 | h969
                          · linarith only [h957, h960, h969, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                          · linarith only [h957, h960, h962, h963, h969, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h973 | h973
                        · linarith only [h0, h956, h973, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · linarith only [h957, h961, h972, h973, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h976 | h976
                        · linarith only [h0, h956, h976, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h978 | h978
                          · linarith only [h957, h960, h962, h978, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases h1bigk with h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h0, hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h668, hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h814, hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h954, hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hc01, hlam, hphi, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h961, h972, h978, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h814, hc01, hlam, hphi, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h814, h962, hc01, hlam, hphi, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hc01, hlam, hphi, p980_1, u1elo2]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h957, hlam, p980_1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h814, h957, hc01, hlam, hphi, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h814, h957, h962, hc01, hlam, hphi, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hc01, hlam, hphi, p980_1, u1elo3]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h958, hlam, p980_1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h960, hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h962, hlam, p980_1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hc01, hlam, hphi, p980_1, u1elo4]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h959, hlam, p980_1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h961, hlam, p980_0]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [h814, h957, h961, hc01, hlam, hphi, p980_1, u1elo1]
                            · have p980_0 := h980c.1
                              have p980_1 := h980c.2.1
                              have p980_2 := h980c.2.2.1
                              have p980_3 := h980c.2.2.2
                              linarith only [hlam, p980_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1006 | h1006
                    · linarith only [h1006, h960, h961, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1009 | h1009
                        · linarith only [h0, h1009, h956, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1011 | h1011
                          · linarith only [h1006, h1011, h814, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h1bigk with h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h0, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h668, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h814, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h954, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h668, hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h814, hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h954, hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hc01, hlam, hphi, p1013_1, u1elo2]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h957, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h814, h957, hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h961, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hc01, hlam, hphi, p1013_1, u1elo3]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h958, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h960, hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h1006, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hc01, hlam, hphi, p1013_1, u1elo4]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h959, hlam, p1013_1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h668, h959, hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [h814, h959, hc01, hlam, hphi, p1013_1, u1elo1]
                            · have p1013_0 := h1013c.1
                              have p1013_1 := h1013c.2.1
                              have p1013_2 := h1013c.2.2.1
                              have p1013_3 := h1013c.2.2.2
                              linarith only [hlam, p1013_0]
                      · linarith only [h1008, h960, h961, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1040 | h1040
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1041 | h1041
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1042 | h1042
                      · linarith only [h1040, h1042, h960, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1044 | h1044
                        · linarith only [h0, h1044, h956, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · linarith only [h1040, h1044, h960, hc23, hc34, hlam, hphi]
                    · linarith only [h1040, h1041, h960, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1048 | h1048
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1049 | h1049
                      · linarith only [h1049, h668, h960, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1051 | h1051
                        · linarith only [h0, h1051, h956, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1053 | h1053
                          · rcases h1bigk with h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h0, hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h668, hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h814, hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h954, hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hc01, hlam, hphi, p1054_1, u1elo1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h668, hc01, hlam, hphi, p1054_1, u1elo1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h1048, hlam, hphi, ht01, ht0b, ht5b, p1054_1, u1elo1, u5ehi1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h954, hc01, hlam, hphi, p1054_1, u1elo1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hc01, hlam, hphi, p1054_1, u1elo2]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h957, hlam, p1054_1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h960, hlam, p1054_1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h1040, hlam, p1054_1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hc01, hlam, hphi, p1054_1, u1elo3]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h958, hlam, p1054_1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h668, h958, hc01, hlam, hphi, p1054_1, u1elo1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h1040, h668, h958, hc01, hlam, hphi, p1054_1, u1elo1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hc01, hlam, hphi, p1054_1, u1elo4]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h959, hlam, p1054_1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h668, h959, hc01, hlam, hphi, p1054_1, u1elo1]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [h1048, hlam, p1054_0]
                            · have p1054_0 := h1054c.1
                              have p1054_1 := h1054c.2.1
                              have p1054_2 := h1054c.2.2.1
                              have p1054_3 := h1054c.2.2.2
                              linarith only [hlam, p1054_0]
                          · linarith only [h1053, h668, h960, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1081 | h1081
                      · linarith only [h0, h1081, h668, h956, h960, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1083 | h1083
                        · linarith only [h0, h1083, h956, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1085 | h1085
                          · linarith only [h1048, h1085, h814, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1085, h668, h960, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h1089, h957, h959, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1091 | h1091
                    · linarith only [h1091, h958, h959, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1093 | h1093
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1094 | h1094
                        · linarith only [h0, h1089, h1094, h956, h959, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1096 | h1096
                          · linarith only [h0, h1091, h1093, h1094, h1096, h814, h956, h959, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h1093, h1094, h1096, h956, h959, hc34, hc45, hlam, hphi]
                      · linarith only [h1088, h1089, h1093, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1100 | h1100
                  · linarith only [h1100, h957, h959, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1102 | h1102
                    · linarith only [h1102, h958, h959, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1104 | h1104
                      · linarith only [h1088, h1104, h668, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1106 | h1106
                        · linarith only [h1100, h1106, h668, h956, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1108 | h1108
                          · linarith only [h1102, h1108, h814, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1088, h1108, h668, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1111 | h1111
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                · linarith only [h1112, h957, h958, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1114 | h1114
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1115 | h1115
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1116 | h1116
                      · linarith only [h1112, h1114, h1116, h956, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1118 | h1118
                        · linarith only [h0, h1116, h1118, h956, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1114, h1116, h1118, h957, h958, hc23, hc34, hlam, hphi]
                    · linarith only [h1114, h1115, h957, h958, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1122 | h1122
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1123 | h1123
                      · linarith only [h1112, h1123, h668, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1125 | h1125
                        · linarith only [h0, h1114, h1123, h1125, h668, h956, h958, hc01, hc34, hlam, hphi, ht12, ht23]
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
                              linarith only [h0, hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h668, hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h814, hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h954, hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1123, h958, hc01, hc34, hlam, hphi, ht12, ht23, p1128_1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1123, h668, h958, hc01, hc34, hlam, hphi, ht12, ht23, p1128_1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h958, hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1123, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1128_1, u5ehi1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hc01, hlam, hphi, p1128_1, u1elo2]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h957, hlam, p1128_1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1112, hlam, p1128_1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1114, hlam, p1128_1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hc01, hlam, hphi, p1128_1, u1elo3]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h0, h956, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1128_1, u1elo3]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h668, hc01, hlam, hphi, p1128_1, u1elo3]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1114, h668, hc01, hlam, hphi, p1128_1, u1elo3]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hc01, hlam, hphi, p1128_1, u1elo4]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1111, hlam, p1128_1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1111, h668, hc01, hlam, hphi, p1128_1, u1elo1]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [h1122, hlam, p1128_0]
                            · have p1128_0 := h1128c.1
                              have p1128_1 := h1128c.2.1
                              have p1128_2 := h1128c.2.2.1
                              have p1128_3 := h1128c.2.2.2
                              linarith only [hlam, p1128_0]
                          · linarith only [h0, h1122, h1123, h1127, h958, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h1111, h1122, h958, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1156 | h1156
                · linarith only [h1156, h957, h958, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1158 | h1158
                  · linarith only [h1111, h1158, h957, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1160 | h1160
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1161 | h1161
                      · linarith only [h1156, h1161, h668, h956, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1163 | h1163
                        · linarith only [h0, h1158, h1161, h1163, h668, h956, h958, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1165 | h1165
                          · rcases h1bigk with h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h0, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h668, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h814, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h954, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h1111, h1163, h1165, hc01, hc34, hlam, hphi, ht12, ht23, p1166_1]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h1111, h1163, h1165, h668, hc01, hc34, hlam, hphi, ht12, ht23, p1166_1]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h958, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h1111, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hc01, hlam, hphi, p1166_1, u1elo2]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h957, hlam, p1166_1]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h1156, hlam, p1166_1]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h1158, hlam, p1166_1]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hc01, hlam, hphi, p1166_1, u1elo3]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h0, h956, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1166_1, u1elo3]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h668, hc01, hlam, hphi, p1166_1, u1elo3]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p1166_1, u1elo3, u5ehi1]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hc01, hlam, hphi, p1166_1, u1elo4]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h668, h957, hc01, hlam, hphi, p1166_1, u1elo4]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h668, hc01, hlam, hphi, p1166_1, u1elo4]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [h1160, hlam, p1166_0]
                            · have p1166_0 := h1166c.1
                              have p1166_1 := h1166c.2.1
                              have p1166_2 := h1166c.2.2.1
                              have p1166_3 := h1166c.2.2.2
                              linarith only [hlam, p1166_0]
                          · linarith only [h1160, h1161, h1165, h668, h957, h958, hc01, hlam, hphi, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1193 | h1193
                      · linarith only [h1156, h1193, h668, h956, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1195 | h1195
                        · linarith only [h0, h1160, h1195, h956, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1197 | h1197
                          · linarith only [h0, h1160, h1197, h956, h958, hc23, hc34, hlam, hphi]
                          · linarith only [h1156, h1197, h668, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h956, h957, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1201 | h1201
          · linarith only [h0, h1201, h956, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1203 | h1203
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1204 | h1204
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1205 | h1205
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1206 | h1206
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1207 | h1207
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1208 | h1208
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1209 | h1209
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1210 | h1210
                          · linarith only [h1201, h1203, h1208, h1210, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases h1bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h668, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h814, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h954, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1201, hc01, hc23, hlam, hphi, ht12, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1201, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1201, h1207, h1210, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1201, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1212_1, u5ehi1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hc01, hlam, hphi, p1212_1, u1elo2]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1203, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1212_1, u1elo2]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1207, h1210, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1212_1, u1elo2]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h954, hc01, hlam, hphi, p1212_1, u1elo2]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1203, hc01, hlam, hphi, p1212_1, u1elo1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1203, hlam, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1205, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1201, h1203, h954, hc01, hc23, hlam, hphi, ht12, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hc01, hlam, hphi, p1212_1, u1elo4]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1204, hlam, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1206, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1207, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                        · linarith only [h0, h1201, h1209, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1201, h1203, h1207, h1208, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1240 | h1240
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1241 | h1241
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1242 | h1242
                          · linarith only [h1207, h1240, h1242, h814, hc01, hc24, hlam, hphi, ht12]
                          · rcases h1bigk with h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h0, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h668, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h814, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h954, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc01, hlam, hphi, p1244_1, u1elo1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1201, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1201, h814, hc01, hc23, hlam, hphi, ht12, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1201, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1244_1, u5ehi1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc01, hlam, hphi, p1244_1, u1elo2]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1203, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1244_1, u1elo2]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h814, hc01, hlam, hphi, p1244_1, u1elo2]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h954, hc01, hlam, hphi, p1244_1, u1elo2]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc01, hlam, hphi, p1244_1, u1elo3]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1203, hlam, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1205, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1207, hlam, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc01, hlam, hphi, p1244_1, u1elo4]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1204, hlam, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1206, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1204, h814, hc01, hlam, hphi, p1244_1, u1elo1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                        · linarith only [h1201, h1206, h1241, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · linarith only [h1201, h1204, h1207, h1240, h814, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1201, h1204, h1206, hlam]
                · linarith only [h1201, h1203, h1205, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1274 | h1274
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1275 | h1275
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1276 | h1276
                    · linarith only [h1203, h1204, h1276, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1280 | h1280
                          · linarith only [h1203, h1276, h1278, h1280, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases h1bigk with h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h0, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h668, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h814, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h954, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1204, h1275, hc01, hlam, hphi, p1282_1, u1elo2]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1201, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1204, h1275, h814, hc01, hlam, hphi, p1282_1, u1elo2]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1204, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hc01, hlam, hphi, p1282_1, u1elo2]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1203, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1282_1, u1elo2]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h814, hc01, hlam, hphi, p1282_1, u1elo2]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p1282_1, u1elo2, u5ehi1]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1203, hc01, hlam, hphi, p1282_1, u1elo1]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1203, hlam, p1282_1]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1274, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1276, hlam, p1282_1]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hc01, hlam, hphi, p1282_1, u1elo4]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1282_1, u1elo4]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1275, hlam, p1282_0]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [h1275, h814, hc01, hlam, hphi, p1282_1, u1elo2]
                            · have p1282_0 := h1282c.1
                              have p1282_1 := h1282c.2.1
                              have p1282_2 := h1282c.2.2.1
                              have p1282_3 := h1282c.2.2.2
                              linarith only [hlam, p1282_0]
                        · linarith only [h0, h1275, h1279, h956, hc01, hlam, hphi, u1elo2]
                      · linarith only [h1201, h1203, h1278, h814, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1310 | h1310
                    · linarith only [h1203, h1204, h1310, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1312 | h1312
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1313 | h1313
                        · linarith only [h1275, h1313, h668, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1201, h1203, h1313, h814, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1201, h1203, h1312, h814, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1201, h1203, h1274, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1318 | h1318
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1319 | h1319
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1320 | h1320
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1321 | h1321
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1322 | h1322
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1323 | h1323
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1324 | h1324
                          · linarith only [h1319, h1324, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                          · rcases h1bigk with h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c | h1326c
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h0, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h668, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h814, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h954, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hc01, hlam, hphi, p1326_1, u1elo1]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1201, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1203, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p1326_1, u1elo1, u5ehi1]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hc01, hlam, hphi, p1326_1, u1elo2]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1326_1, u1elo2]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1321, h1324, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1326_1, u1elo2]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h954, hc01, hlam, hphi, p1326_1, u1elo2]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hc01, hlam, hphi, p1326_1, u1elo3]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1318, h1323, hlam, hphi, ht01, ht0b, ht5b, p1326_1, u1elo3, u5ehi3]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1319, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1319, h954, hc01, hlam, hphi, p1326_1, u1elo2]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hc01, hlam, hphi, p1326_1, u1elo4]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1318, hlam, p1326_1]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1320, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [h1321, hlam, p1326_0]
                            · have p1326_0 := h1326c.1
                              have p1326_1 := h1326c.2.1
                              have p1326_2 := h1326c.2.2.1
                              have p1326_3 := h1326c.2.2.2
                              linarith only [hlam, p1326_0]
                        · linarith only [h0, h1203, h1322, h1323, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1201, h1318, h1322, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1203, h1318, h1321, hlam]
                  · linarith only [h1201, h1318, h1320, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1356 | h1356
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1357 | h1357
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1358 | h1358
                      · linarith only [h1201, h1318, h1319, h1358, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h1201, h1318, h1358, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1201, h1318, h1319, h1357, hlam]
                  · linarith only [h1201, h1318, h1356, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1364 | h1364
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1365 | h1365
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1366 | h1366
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1367 | h1367
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1368 | h1368
                          · linarith only [h1363, h1368, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                          · rcases h1bigk with h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h0, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h668, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h814, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h954, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hc01, hlam, hphi, p1370_1, u1elo1]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1201, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1203, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1318, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hc01, hlam, hphi, p1370_1, u1elo2]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1370_1, u1elo2]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1365, h1368, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1370_1, u1elo2]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p1370_1, u1elo2, u5ehi1]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hc01, hlam, hphi, p1370_1, u1elo3]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1370_1, u1elo3]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1363, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h0, h1318, h1363, hc01, hlam, hphi, p1370_1, u1elo2]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hc01, hlam, hphi, p1370_1, u1elo4]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1370_1, u1elo4]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1364, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [h1365, hlam, p1370_0]
                            · have p1370_0 := h1370c.1
                              have p1370_1 := h1370c.2.1
                              have p1370_2 := h1370c.2.2.1
                              have p1370_3 := h1370c.2.2.2
                              linarith only [hlam, p1370_0]
                        · linarith only [h0, h1201, h1367, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h1201, h1366, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1398 | h1398
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1399 | h1399
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1400 | h1400
                          · linarith only [h1363, h1365, h1400, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases h1bigk with h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h0, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h668, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h814, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h954, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hc01, hlam, hphi, p1402_1, u1elo1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1201, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1203, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1318, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hc01, hlam, hphi, p1402_1, u1elo2]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1402_1, u1elo2]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h814, hc01, hlam, hphi, p1402_1, u1elo2]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p1402_1, u1elo2, u5ehi1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hc01, hlam, hphi, p1402_1, u1elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1402_1, u1elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1363, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1365, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hc01, hlam, hphi, p1402_1, u1elo4]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, p1402_1, u1elo4]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1364, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1364, h814, hc01, hlam, hphi, p1402_1, u1elo2]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                        · linarith only [h0, h1364, h1399, h956, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h1201, h1398, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1430 | h1430
                    · linarith only [h1363, h1364, h1430, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1432 | h1432
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1433 | h1433
                        · linarith only [h0, h1203, h1363, h1364, h1433, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1201, h1433, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h1201, h1363, h1432, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1437 | h1437
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1438 | h1438
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1439 | h1439
                      · linarith only [h1363, h1437, h1439, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h1201, h1439, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1363, h1437, h1438, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1443 | h1443
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1444 | h1444
                      · linarith only [h1363, h1444, h668, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1201, h1444, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1447 | h1447
                      · linarith only [h0, h1201, h1363, h1447, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h1201, h1447, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_21_15_M_LI_L_R (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_M_LI_L_R_x0 m hb1 hb5 h0
  · exact r1l7_21_15_M_LI_L_R_x1 m hb1 hb5 h0

end R2N4
