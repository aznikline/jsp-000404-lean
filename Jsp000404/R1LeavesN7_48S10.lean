import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h691 | h691
  · rcases m.htr 0 3 4 (by decide) (by decide) with h692 | h692
    · linarith only [h3, h4, h692, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h694 | h694
      · rcases m.htr 0 4 5 (by decide) (by decide) with h695 | h695
        · rcases m.htr 1 2 3 (by decide) (by decide) with h696 | h696
          · rcases m.htr 1 2 4 (by decide) (by decide) with h697 | h697
            · linarith only [h4, h697, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
              · rcases m.htr 1 3 4 (by decide) (by decide) with h700 | h700
                · linarith only [h0, h4, h692, h694, h696, h700, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h702 | h702
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h703 | h703
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h704 | h704
                      · linarith only [h692, h694, h704, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h706 | h706
                        · linarith only [h0, h4, h696, h706, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h3, h4, h694, h706, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h4, h695, h697, h703, hc12, hlam, hphi, u2elo3]
                  · linarith only [h3, h4, h694, h702, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h4, h691, h696, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h3, h4, h696, hc12, hlam, hphi, u2elo3]
        · linarith only [h3, h4, h694, h695, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h714 | h714
        · rcases m.htr 1 2 3 (by decide) (by decide) with h715 | h715
          · rcases m.htr 1 2 4 (by decide) (by decide) with h716 | h716
            · linarith only [h4, h716, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
              · rcases m.htr 1 3 4 (by decide) (by decide) with h719 | h719
                · linarith only [h0, h4, h692, h715, h719, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h721 | h721
                  · linarith only [h3, h694, h719, h721, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h723 | h723
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h724 | h724
                      · linarith only [h3, h4, h724, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h726 | h726
                        · linarith only [h0, h4, h694, h715, h726, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h728 | h728
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h729 | h729
                            · rcases h0bigk with h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h0, h718, h726, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                rcases p730_3 (m.d 0 1) (by simp) with h733 | h733
                                · rcases p730_3 (m.d 0 2) (by simp) with h734 | h734
                                  · linarith only [h0, h734, hlam]
                                  · linarith only [h3, h734, hlam]
                                · linarith only [h733, hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h0, h4, h718, h726, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                rcases p730_3 (m.d 0 1) (by simp) with h739 | h739
                                · rcases p730_3 (m.d 0 2) (by simp) with h740 | h740
                                  · linarith only [h0, h740, hlam]
                                  · linarith only [h691, h740, hlam]
                                · linarith only [h2, h739, hlam]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h0, hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p730_1, u2elo3]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h4, hlam, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p730_1, u2elo3]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h694, hc01, hc35, hlam, hphi, ht12, ht23, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h3, hlam, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h692, hlam, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h694, hlam, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h1, hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h691, h726, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p730_1, u2elo3]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p730_1, u2elo3]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h2, hlam, p730_0]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h691, hlam, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h3, h4, h691, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p730_1, u2elo3]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [h714, hlam, p730_1]
                              · have p730_0 := h730c.1
                                have p730_1 := h730c.2.1
                                have p730_2 := h730c.2.2.1
                                have p730_3 := h730c.2.2.2
                                linarith only [hlam, p730_0]
                            · linarith only [h0, h4, h718, h724, h728, h729, hlam]
                          · linarith only [h3, h4, h728, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h4, h691, h714, h715, h716, h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h4, h691, h715, h718, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h3, h4, h715, hc12, hlam, hphi, u2elo3]
        · linarith only [h4, h691, h714, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h770 | h770
    · linarith only [h3, h4, h770, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h772 | h772
      · linarith only [h3, h691, h772, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h774 | h774
        · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
          · rcases m.htr 1 2 4 (by decide) (by decide) with h776 | h776
            · linarith only [h4, h776, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h778 | h778
              · linarith only [h0, h691, h778, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h780 | h780
                · linarith only [h0, h4, h770, h775, h780, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h782 | h782
                  · linarith only [h3, h691, h772, h780, h782, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h784 | h784
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h785 | h785
                      · linarith only [h0, h4, h775, h785, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
                        · linarith only [h0, h4, h775, h782, h787, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h789 | h789
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h790 | h790
                            · rcases h0bigk with h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h0, h775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                rcases p791_3 (m.d 0 1) (by simp) with h794 | h794
                                · rcases p791_3 (m.d 0 2) (by simp) with h795 | h795
                                  · linarith only [h0, h795, hlam]
                                  · linarith only [h3, h795, hlam]
                                · linarith only [h794, hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h0, h691, h774, h775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h0, h691, h775, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h0, hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h3, h691, h789, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p791_1, u2elo3]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h4, hlam, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h691, hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h3, hlam, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h770, hlam, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h772, hlam, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h1, hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h3, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p791_1, u2elo3]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h4, h691, hc02, hlam, hphi, p791_1, u2elo3]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h2, hlam, p791_0]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h3, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h3, h691, h789, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p791_1, u2elo3]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [h774, hlam, p791_1]
                              · have p791_0 := h791c.1
                                have p791_1 := h791c.2.1
                                have p791_2 := h791c.2.2.1
                                have p791_3 := h791c.2.2.2
                                linarith only [hlam, p791_0]
                            · linarith only [h0, h4, h775, h785, h790, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1, h4, h784, h789, hlam]
                    · linarith only [h4, h774, h775, h776, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h3, h775, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
          · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
            · linarith only [h0, h4, h826, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h828 | h828
              · linarith only [h0, h691, h828, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
                · linarith only [h1, h770, h825, h826, h830, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h832 | h832
                  · linarith only [h0, h3, h691, h772, h825, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
                    · linarith only [h1, h774, h834, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                      · linarith only [h0, h691, h770, h825, h836, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h838 | h838
                        · linarith only [h3, h4, h772, h838, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h840 | h840
                          · linarith only [h0, h4, h774, h825, h840, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · linarith only [h0, h4, h825, h840, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h3, h4, h825, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h844 | h844
  · rcases m.htr 0 2 5 (by decide) (by decide) with h845 | h845
    · rcases m.htr 0 3 4 (by decide) (by decide) with h846 | h846
      · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
        · rcases m.htr 0 4 5 (by decide) (by decide) with h848 | h848
          · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
            · linarith only [h3, h849, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h851 | h851
              · rcases m.htr 1 2 5 (by decide) (by decide) with h852 | h852
                · rcases m.htr 1 3 4 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h854 | h854
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h856 | h856
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h858 | h858
                            · linarith only [h0, h3, h851, h858, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · linarith only [h3, h844, h848, h856, h858, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h0, h3, h847, h852, h857, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h3, h846, h851, h856, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h3, h844, h848, h855, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h3, h847, h849, h851, h854, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h3, h846, h849, h851, h853, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h3, h845, h851, h852, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h3, h844, h851, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h868 | h868
            · linarith only [h3, h868, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
              · rcases m.htr 1 2 5 (by decide) (by decide) with h871 | h871
                · rcases m.htr 1 3 4 (by decide) (by decide) with h872 | h872
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h873 | h873
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h874 | h874
                      · linarith only [h1, h848, h874, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h876 | h876
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h877 | h877
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h878 | h878
                            · linarith only [h0, h1, h3, h848, h870, h878, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h880 | h880
                              · linarith only [h1, h848, h870, h876, h880, hlam]
                              · rcases h0bigk with h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c | h882c
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h0, h871, h878, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p882_1]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h0, h3, h871, h876, h878, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p882_1]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  rcases p882_3 (m.d 0 1) (by simp) with h886 | h886
                                  · rcases p882_3 (m.d 0 2) (by simp) with h887 | h887
                                    · linarith only [h0, h887, hlam]
                                    · linarith only [h844, h887, hlam]
                                  · linarith only [h1, h886, hlam]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  rcases p882_3 (m.d 0 1) (by simp) with h891 | h891
                                  · rcases p882_3 (m.d 0 2) (by simp) with h892 | h892
                                    · linarith only [h0, h892, hlam]
                                    · linarith only [h845, h892, hlam]
                                  · linarith only [h2, h891, hlam]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h0, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h3, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h1, h3, h870, h876, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p882_1, u2elo2]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p882_1, u2elo2]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h0, h871, h876, h878, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p882_1]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h3, hc02, hlam, hphi, p882_1, u2elo2]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h1, h3, h870, h876, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p882_1, u2elo2]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h2, h3, h870, h874, h876, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p882_1, u2elo2]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h1, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h844, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h846, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h848, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h2, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h845, hlam, p882_1]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h847, hlam, p882_0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [h1, h845, h870, h876, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p882_1, u2elo0]
                                · have p882_0 := h882c.1
                                  have p882_1 := h882c.2.1
                                  have p882_2 := h882c.2.2.1
                                  have p882_3 := h882c.2.2.2
                                  linarith only [hlam, p882_0]
                          · linarith only [h3, h847, h877, hlam]
                        · linarith only [h3, h846, h876, hlam]
                    · linarith only [h3, h847, h868, h870, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h3, h846, h868, h870, h872, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h845, h870, h871, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · linarith only [h3, h844, h870, hc12, hlam, hphi, u2elo2]
        · linarith only [h3, h845, h847, hlam]
      · linarith only [h3, h844, h846, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h924 | h924
      · rcases m.htr 0 3 5 (by decide) (by decide) with h925 | h925
        · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
          · linarith only [h844, h845, h926, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
            · linarith only [h3, h928, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h930 | h930
              · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
                · linarith only [h0, h845, h931, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h933 | h933
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h934 | h934
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h935 | h935
                      · linarith only [h1, h926, h935, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h937 | h937
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h938 | h938
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h939 | h939
                            · linarith only [h0, h1, h845, h926, h930, h938, h939, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h941 | h941
                              · linarith only [h0, h845, h930, h937, h939, h941, hlam]
                              · rcases h0bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, h930, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, h3, h930, h937, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  rcases p943_3 (m.d 0 1) (by simp) with h947 | h947
                                  · rcases p943_3 (m.d 0 2) (by simp) with h948 | h948
                                    · linarith only [h0, h948, hlam]
                                    · linarith only [h844, h948, hlam]
                                  · linarith only [h1, h947, hlam]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, h845, h930, h937, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h3, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h1, h845, h930, h937, h938, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h845, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h3, hc02, hlam, hphi, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h1, h3, h930, h937, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h3, h844, h845, h937, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo2]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h1, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h844, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h924, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h926, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h2, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h844, h937, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h925, hlam, p943_0]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [h1, h845, h930, h937, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo4]
                                · have p943_0 := h943c.1
                                  have p943_1 := h943c.2.1
                                  have p943_2 := h943c.2.2.1
                                  have p943_3 := h943c.2.2.2
                                  linarith only [hlam, p943_0]
                          · linarith only [h3, h925, h938, hlam]
                        · linarith only [h3, h924, h937, hlam]
                    · linarith only [h3, h925, h928, h934, hc12, hlam, hphi, u2elo2]
                  · linarith only [h3, h924, h928, h930, h933, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h3, h844, h930, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h978 | h978
          · linarith only [h3, h844, h925, h978, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h980 | h980
            · linarith only [h3, h980, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h982 | h982
              · rcases m.htr 1 2 5 (by decide) (by decide) with h983 | h983
                · linarith only [h0, h845, h983, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h985 | h985
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                    · linarith only [h0, h3, h925, h980, h982, h986, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h988 | h988
                      · linarith only [h1, h978, h988, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h990 | h990
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                          · linarith only [h0, h3, h925, h982, h990, h991, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h993 | h993
                            · linarith only [h0, h1, h978, h982, h993, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                              · linarith only [h0, h3, h982, h990, h991, h993, h995, hlam]
                              · linarith only [h0, h3, h982, h991, h995, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h3, h924, h982, h990, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h924, h925, h985, hc13, hc35, hlam, hphi]
              · linarith only [h3, h844, h982, hc12, hlam, hphi, u2elo2]
      · linarith only [h3, h844, h924, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1002 | h1002
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1003 | h1003
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1004 | h1004
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1006 | h1006
            · linarith only [h1006, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1008 | h1008
              · linarith only [h0, h1008, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1011 | h1011
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1012 | h1012
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1013 | h1013
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1014 | h1014
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1015 | h1015
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1016 | h1016
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1017 | h1017
                              · rcases h0bigk with h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h0, h1010, h1015, h1017, hc01, hc45, hlam, hphi, ht0b, ht5b, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1003, h1017, hc01, hc45, hlam, hphi, ht0b, ht5b, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h0, h1010, h1015, h1017, h844, hc01, hc45, hlam, hphi, ht0b, ht5b, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  rcases p1018_3 (m.d 0 1) (by simp) with h1023 | h1023
                                  · rcases p1018_3 (m.d 0 2) (by simp) with h1024 | h1024
                                    · linarith only [h0, h1024, hlam]
                                    · linarith only [h1002, h1024, hlam]
                                  · linarith only [h1023, h2, hlam]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h0, hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h3, hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h844, hlam, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1014, h2, h844, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1018_1, u2elo2]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h3, hc01, hlam, hphi, ht12, p1018_1, u2elo2]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h3, hc02, hlam, hphi, p1018_1, u2elo2]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1018_1, u2elo2]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1002, h1015, h1017, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1018_1, u2elo2]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1, hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h0, h1010, h1015, h1017, hc04, hc45, hlam, hphi, ht0b, ht5b, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1003, hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1002, h1014, h1015, h1017, h844, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1018_1, u2elo2]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h2, hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1002, hlam, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1004, hlam, p1018_0]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [h1005, hlam, p1018_1]
                                · have p1018_0 := h1018c.1
                                  have p1018_1 := h1018c.2.1
                                  have p1018_2 := h1018c.2.2.1
                                  have p1018_3 := h1018c.2.2.2
                                  linarith only [hlam, p1018_0]
                              · linarith only [h1002, h1016, h1017, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h0, h1010, h1013, h1016, h844, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h1004, h1015, h3, hlam]
                        · linarith only [h1003, h1014, h3, hlam]
                      · linarith only [h1002, h1005, h1008, h1013, h844, hc12, hlam, hphi, u2elo3]
                    · linarith only [h1004, h1006, h1010, h1012, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h1003, h1006, h1010, h1011, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1002, h1010, h844, hc12, hlam, hphi, u2elo3]
          · linarith only [h1002, h1005, h844, hlam]
        · linarith only [h1002, h1004, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1058 | h1058
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1059 | h1059
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1060 | h1060
            · linarith only [h1060, h3, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1062 | h1062
              · linarith only [h0, h1062, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1064 | h1064
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1065 | h1065
                  · linarith only [h1003, h1060, h1065, h3, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1067 | h1067
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1068 | h1068
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1069 | h1069
                        · linarith only [h0, h1003, h1064, h1069, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1071 | h1071
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1072 | h1072
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1073 | h1073
                              · rcases h0bigk with h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, h1064, h1071, h1073, hc01, hc45, hlam, hphi, ht0b, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, h1064, h1071, h1073, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, h1064, h1071, h1073, h844, hc01, hc45, hlam, hphi, ht0b, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  rcases p1074_3 (m.d 0 1) (by simp) with h1079 | h1079
                                  · rcases p1074_3 (m.d 0 2) (by simp) with h1080 | h1080
                                    · linarith only [h0, h1080, hlam]
                                    · linarith only [h1002, h1080, hlam]
                                  · linarith only [h1079, h2, hlam]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h3, hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h844, hlam, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1069, h3, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, h1003, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, h1064, h1071, h1073, hc03, hc45, hlam, hphi, ht0b, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1003, hlam, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1002, h1069, h1071, h1073, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1, hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h0, h1064, h1071, h1073, h844, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1074_1, u2elo3]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h844, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1074_1, u2elo3]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1002, h1071, h1073, h844, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1074_1, u2elo3]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h2, hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1002, hlam, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1058, hlam, p1074_0]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [h1059, hlam, p1074_1]
                                · have p1074_0 := h1074c.1
                                  have p1074_1 := h1074c.2.1
                                  have p1074_2 := h1074c.2.2.1
                                  have p1074_3 := h1074c.2.2.2
                                  linarith only [hlam, p1074_0]
                              · linarith only [h0, h1064, h1069, h1071, h1073, h3, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h1059, h1072, h844, hlam]
                          · linarith only [h0, h1058, h1064, h1071, h3, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1002, h1059, h1062, h1064, h1068, h844, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1003, h1058, h1060, h1064, h1067, h844, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h1002, h1064, h844, hc12, hlam, hphi, u2elo3]
          · linarith only [h1002, h1003, h1059, h3, hlam]
        · linarith only [h1002, h1058, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1112 | h1112
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1113 | h1113
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1114 | h1114
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1115 | h1115
            · linarith only [h0, h1115, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1117 | h1117
              · linarith only [h0, h1117, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
                · linarith only [h0, h1002, h1119, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1122 | h1122
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1123 | h1123
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1124 | h1124
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1125 | h1125
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1126 | h1126
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1127 | h1127
                              · rcases h0bigk with h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c
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
                                  · rcases p1128_3 (m.d 0 2) (by simp) with h1131 | h1131
                                    · linarith only [h0, h1131, hlam]
                                    · rcases p1128_3 (m.d 0 3) (by simp) with h1133 | h1133
                                      · linarith only [h1133, h3, hc02, hlam, hphi, p1128_1, u2elo2]
                                      · linarith only [h1133, h3, hlam]
                                  · linarith only [h0, h1130, hlam]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1112, h1127, hc01, hc45, hlam, hphi, ht0b, ht5b, p1128_1]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1, h1121, h1127, hc01, hc45, hlam, hphi, ht0b, ht5b, p1128_1]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  rcases p1128_3 (m.d 0 1) (by simp) with h1139 | h1139
                                  · rcases p1128_3 (m.d 0 2) (by simp) with h1140 | h1140
                                    · linarith only [h0, h1140, hlam]
                                    · rcases p1128_3 (m.d 0 3) (by simp) with h1142 | h1142
                                      · linarith only [h1142, h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1128_1, u2elo2]
                                      · linarith only [h1113, h1142, hlam]
                                  · linarith only [h1139, h2, hlam]
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
                                  linarith only [h3, hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h844, hlam, p1128_1]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1002, hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h3, hc01, hlam, hphi, ht12, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1, h1121, h1127, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h0, h1002, h3, hc12, hlam, hphi, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1, hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h0, h1124, h844, hc12, hlam, hphi, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1112, hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h0, h1002, h1124, h844, hc12, hlam, hphi, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h2, hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h0, h1002, h1124, h1126, hc12, hlam, hphi, p1128_1, u2elo2]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1113, hlam, p1128_0]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [h1114, hlam, p1128_1]
                                · have p1128_0 := h1128c.1
                                  have p1128_1 := h1128c.2.1
                                  have p1128_2 := h1128c.2.2.1
                                  have p1128_3 := h1128c.2.2.2
                                  linarith only [hlam, p1128_0]
                              · rcases h0bigk with h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  rcases p1166_3 (m.d 0 1) (by simp) with h1168 | h1168
                                  · rcases p1166_3 (m.d 0 2) (by simp) with h1169 | h1169
                                    · linarith only [h0, h1169, hlam]
                                    · rcases p1166_3 (m.d 0 3) (by simp) with h1171 | h1171
                                      · linarith only [h0, h1171, h3, hc12, hlam, hphi, p1166_1, u2elo2]
                                      · linarith only [h1171, h3, hlam]
                                  · linarith only [h0, h1168, hlam]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1114, h1127, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1123, h1127, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h0, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h3, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h844, hlam, p1166_1]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1002, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h0, h1, h1123, h1124, h1127, h844, hc03, hc12, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1, u2elo2]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p1166_1, u2elo2]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1, h1123, h1127, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1166_1, u2elo2]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1123, h1127, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1166_1, u2elo2]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h0, h844, hc12, hlam, hphi, p1166_1, u2elo3]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1112, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1112, h1123, h1127, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1166_1, u2elo2]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h2, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h0, h1002, hc12, hlam, hphi, p1166_1, u2elo4]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1113, hlam, p1166_0]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [h1114, hlam, p1166_1]
                                · have p1166_0 := h1166c.1
                                  have p1166_1 := h1166c.2.1
                                  have p1166_2 := h1166c.2.2.1
                                  have p1166_3 := h1166c.2.2.2
                                  linarith only [hlam, p1166_0]
                            · linarith only [h0, h1, h1123, h1126, h844, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1113, h1125, h3, hlam]
                        · linarith only [h1112, h1124, h3, hlam]
                      · linarith only [h1112, h1114, h1117, h1123, h3, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1113, h1121, h1122, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1112, h1115, h1121, h3, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
            · linarith only [h0, h1204, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1206 | h1206
              · linarith only [h0, h1206, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
                · linarith only [h0, h1002, h1208, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1210 | h1210
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1211 | h1211
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1212 | h1212
                      · linarith only [h1, h1114, h1212, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1214 | h1214
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1215 | h1215
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                            · linarith only [h1114, h1214, h1216, h844, hc02, hlam, hphi, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1218 | h1218
                              · linarith only [h1112, h1114, h1218, hlam]
                              · rcases h0bigk with h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  rcases p1220_3 (m.d 0 1) (by simp) with h1222 | h1222
                                  · rcases p1220_3 (m.d 0 2) (by simp) with h1223 | h1223
                                    · linarith only [h0, h1223, hlam]
                                    · rcases p1220_3 (m.d 0 3) (by simp) with h1225 | h1225
                                      · linarith only [h0, h1225, h3, hc12, hlam, hphi, p1220_1, u2elo2]
                                      · linarith only [h1225, h3, hlam]
                                  · linarith only [h0, h1222, hlam]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1220_1]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  rcases p1220_3 (m.d 0 1) (by simp) with h1230 | h1230
                                  · rcases p1220_3 (m.d 0 2) (by simp) with h1231 | h1231
                                    · linarith only [h0, h1231, hlam]
                                    · rcases p1220_3 (m.d 0 3) (by simp) with h1233 | h1233
                                      · linarith only [h0, h1233, h3, h844, hc12, hlam, hphi, p1220_1, u2elo2]
                                      · linarith only [h1112, h1233, hlam]
                                  · linarith only [h1, h1230, hlam]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  rcases p1220_3 (m.d 0 1) (by simp) with h1237 | h1237
                                  · rcases p1220_3 (m.d 0 2) (by simp) with h1238 | h1238
                                    · linarith only [h0, h1238, hlam]
                                    · rcases p1220_3 (m.d 0 3) (by simp) with h1240 | h1240
                                      · linarith only [h0, h1114, h1240, h3, h844, hc12, hlam, hphi, p1220_1, u2elo2]
                                      · linarith only [h1113, h1240, hlam]
                                  · linarith only [h1237, h2, hlam]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h0, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h3, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h844, hlam, p1220_1]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1002, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h3, hc01, hlam, hphi, ht12, p1220_1, u2elo2]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p1220_1, u2elo2]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h0, h3, h844, hc12, hlam, hphi, p1220_1, u2elo2]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h0, h1114, h3, h844, hc12, hlam, hphi, p1220_1, u2elo2]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h0, h844, hc12, hlam, hphi, p1220_1, u2elo3]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1112, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1114, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h2, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h0, h1002, hc12, hlam, hphi, p1220_1, u2elo4]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1113, hlam, p1220_0]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [h1113, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1220_1, u2elo2]
                                · have p1220_0 := h1220c.1
                                  have p1220_1 := h1220c.2.1
                                  have p1220_2 := h1220c.2.2.1
                                  have p1220_3 := h1220c.2.2.2
                                  linarith only [hlam, p1220_0]
                          · linarith only [h1113, h1215, h3, hlam]
                        · linarith only [h1112, h1214, h3, hlam]
                    · linarith only [h1113, h1204, h1211, h3, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1112, h1204, h1210, h3, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1268 | h1268
          · linarith only [h1112, h1113, h1268, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1270 | h1270
            · linarith only [h0, h1270, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1272 | h1272
              · linarith only [h0, h1272, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1274 | h1274
                · linarith only [h0, h1002, h1274, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1276 | h1276
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1277 | h1277
                    · linarith only [h1112, h1113, h1270, h1277, h844, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1279 | h1279
                      · linarith only [h1, h1268, h1279, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1282 | h1282
                          · linarith only [h0, h1113, h1282, h3, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1284 | h1284
                            · linarith only [h0, h1268, h1284, h844, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1286 | h1286
                              · linarith only [h1276, h1277, h1284, h1286, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  rcases p1288_3 (m.d 0 1) (by simp) with h1290 | h1290
                                  · rcases p1288_3 (m.d 0 2) (by simp) with h1291 | h1291
                                    · linarith only [h0, h1291, hlam]
                                    · rcases p1288_3 (m.d 0 3) (by simp) with h1293 | h1293
                                      · linarith only [h0, h1282, h1286, h1293, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1288_1]
                                      · linarith only [h1293, h3, hlam]
                                  · linarith only [h0, h1290, hlam]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  rcases p1288_3 (m.d 0 1) (by simp) with h1298 | h1298
                                  · rcases p1288_3 (m.d 0 2) (by simp) with h1299 | h1299
                                    · linarith only [h0, h1299, hlam]
                                    · rcases p1288_3 (m.d 0 3) (by simp) with h1301 | h1301
                                      · linarith only [h0, h1282, h1286, h1301, h3, h844, hc12, hc45, hlam, hphi, ht23, ht34, p1288_1]
                                      · linarith only [h1112, h1301, hlam]
                                  · linarith only [h1, h1298, hlam]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1112, h1113, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h3, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h844, hlam, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1002, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, h1282, h1286, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, h1282, h1286, h3, h844, hc12, hc45, hlam, hphi, ht23, ht34, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1113, hlam, p1288_1]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, h844, hc12, hlam, hphi, p1288_1, u2elo3]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1112, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1268, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h2, hlam, p1288_0]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, h1002, hc12, hlam, hphi, p1288_1, u2elo4]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h1002, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1288_1, u2elo4]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [h0, h1002, h844, hc12, hlam, hphi, p1288_1, u2elo4]
                                · have p1288_0 := h1288c.1
                                  have p1288_1 := h1288c.2.1
                                  have p1288_2 := h1288c.2.2.1
                                  have p1288_3 := h1288c.2.2.2
                                  linarith only [hlam, p1288_0]
                        · linarith only [h0, h1276, h1277, h1281, h2, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1112, h1113, h1276, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1328 | h1328
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1329 | h1329
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1330 | h1330
            · linarith only [h0, h1330, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1332 | h1332
              · linarith only [h0, h1332, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1334 | h1334
                · linarith only [h0, h1002, h1334, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h1112, h1328, h1330, h1336, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1338 | h1338
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1339 | h1339
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1340 | h1340
                        · linarith only [h1002, h1112, h1328, h1340, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1342 | h1342
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1343 | h1343
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1344 | h1344
                              · rcases h0bigk with h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  rcases p1345_3 (m.d 0 1) (by simp) with h1347 | h1347
                                  · rcases p1345_3 (m.d 0 2) (by simp) with h1348 | h1348
                                    · linarith only [h0, h1348, hlam]
                                    · rcases p1345_3 (m.d 0 3) (by simp) with h1350 | h1350
                                      · linarith only [h0, h1340, h1350, h3, hc12, hc34, hlam, hphi, ht23, p1345_1]
                                      · linarith only [h1350, h3, hlam]
                                  · linarith only [h0, h1347, hlam]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1328, h1344, hc01, hc45, hlam, hphi, ht0b, ht5b, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1, h1336, h1338, h1344, hc01, hc45, hlam, hphi, ht0b, ht5b, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  rcases p1345_3 (m.d 0 1) (by simp) with h1356 | h1356
                                  · rcases p1345_3 (m.d 0 2) (by simp) with h1357 | h1357
                                    · linarith only [h0, h1357, hlam]
                                    · rcases p1345_3 (m.d 0 3) (by simp) with h1359 | h1359
                                      · linarith only [h0, h1002, h1340, h1359, h3, hc12, hc34, hlam, hphi, ht23, p1345_1]
                                      · linarith only [h1328, h1359, hlam]
                                  · linarith only [h1356, h2, hlam]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h0, hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h3, hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h844, hlam, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1002, hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1340, h3, hc01, hc34, hlam, hphi, ht12, ht23, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h0, h1340, h3, hc12, hc34, hlam, hphi, ht23, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1112, hlam, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h0, h1002, h1340, h3, hc12, hc34, hlam, hphi, ht23, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1, hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h0, h844, hc12, hlam, hphi, p1345_1, u2elo3]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h844, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1345_1, u2elo3]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h0, h1002, h844, hc12, hlam, hphi, p1345_1, u2elo3]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h2, hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h0, h1002, hc12, hlam, hphi, p1345_1, u2elo4]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1328, hlam, p1345_0]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [h1329, hlam, p1345_1]
                                · have p1345_0 := h1345c.1
                                  have p1345_1 := h1345c.2.1
                                  have p1345_2 := h1345c.2.2.1
                                  have p1345_3 := h1345c.2.2.2
                                  linarith only [hlam, p1345_0]
                              · linarith only [h0, h1340, h1344, h3, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1, h1339, h1343, h844, hlam]
                          · linarith only [h1328, h1342, h3, hlam]
                      · linarith only [h1329, h1332, h1339, h844, hc12, hlam, hphi, u2elo3]
                    · linarith only [h1112, h1328, h1338, hc13, hc34, hlam, hphi]
          · linarith only [h1112, h1328, h1329, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1389 | h1389
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
            · linarith only [h0, h1390, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1392 | h1392
              · linarith only [h0, h1392, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
                · linarith only [h0, h1002, h1394, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                  · linarith only [h1112, h1390, h1396, h3, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1398 | h1398
                    · linarith only [h0, h1, h1328, h1396, h1398, h3, h844, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1400 | h1400
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1401 | h1401
                        · linarith only [h0, h1112, h1401, h3, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1403 | h1403
                          · linarith only [h0, h1328, h1401, h1403, h3, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1405 | h1405
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1406 | h1406
                              · rcases h0bigk with h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  rcases p1407_3 (m.d 0 1) (by simp) with h1409 | h1409
                                  · rcases p1407_3 (m.d 0 2) (by simp) with h1410 | h1410
                                    · linarith only [h0, h1410, hlam]
                                    · rcases p1407_3 (m.d 0 3) (by simp) with h1412 | h1412
                                      · linarith only [h0, h1403, h1405, h1412, h3, hc12, hlam, hphi, p1407_1, u2elo3]
                                      · linarith only [h1412, h3, hlam]
                                  · linarith only [h0, h1409, hlam]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  rcases p1407_3 (m.d 0 1) (by simp) with h1416 | h1416
                                  · rcases p1407_3 (m.d 0 2) (by simp) with h1417 | h1417
                                    · linarith only [h0, h1417, hlam]
                                    · rcases p1407_3 (m.d 0 3) (by simp) with h1419 | h1419
                                      · linarith only [h1419, hlam, p1407_0]
                                      · rcases p1407_3 (m.d 0 4) (by simp) with h1421 | h1421
                                        · linarith only [h1, h1421, hlam]
                                        · linarith only [h1112, h1421, hlam]
                                  · linarith only [h1416, hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h1389, hc01, hc45, hlam, hphi, ht0b, ht5b, p1407_1]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  rcases p1407_3 (m.d 0 1) (by simp) with h1426 | h1426
                                  · rcases p1407_3 (m.d 0 2) (by simp) with h1427 | h1427
                                    · linarith only [h0, h1427, hlam]
                                    · rcases p1407_3 (m.d 0 3) (by simp) with h1429 | h1429
                                      · linarith only [h1328, h1429, hlam, p1407_1]
                                      · rcases p1407_3 (m.d 0 4) (by simp) with h1431 | h1431
                                        · linarith only [h1, h1431, hlam]
                                        · linarith only [h1389, h1431, hlam]
                                  · linarith only [h1426, h2, hlam]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h0, hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h3, hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h844, hlam, p1407_1]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h1002, hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h0, h1328, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1407_1]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h0, h1403, h1405, h3, hc12, hlam, hphi, p1407_1, u2elo3]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h1112, hlam, p1407_1]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h1328, hlam, p1407_1]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h1, hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h0, h844, hc12, hlam, hphi, p1407_1, u2elo3]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h844, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1407_1, u2elo3]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h844, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1407_1, u2elo3]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h2, hlam, p1407_0]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h0, h1002, h1405, hc12, hlam, hphi, p1407_1, u2elo3]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h0, h1002, h1405, h3, hc12, hlam, hphi, p1407_1, u2elo3]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [h1389, hlam, p1407_1]
                                · have p1407_0 := h1407c.1
                                  have p1407_1 := h1407c.2.1
                                  have p1407_2 := h1407c.2.2.1
                                  have p1407_3 := h1407c.2.2.2
                                  linarith only [hlam, p1407_0]
                              · linarith only [h0, h1, h1112, h1400, h1406, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h1400, h1405, h844, hlam]
                      · linarith only [h1389, h1392, h1400, h844, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1458 | h1458
            · linarith only [h0, h1458, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1460 | h1460
              · linarith only [h0, h1460, h844, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1462 | h1462
                · linarith only [h0, h1002, h1462, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1464 | h1464
                  · linarith only [h1112, h1458, h1464, h3, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1466 | h1466
                    · linarith only [h0, h1, h1328, h1464, h1466, h3, h844, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1468 | h1468
                      · linarith only [h1, h1389, h1468, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                        · linarith only [h0, h1112, h1470, h3, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1472 | h1472
                          · linarith only [h0, h1328, h1472, h3, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1474 | h1474
                            · linarith only [h0, h1389, h1474, h844, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1476 | h1476
                              · linarith only [h0, h1474, h1476, h844, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1470, h1476, h3, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1479 | h1479
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1480 | h1480
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1481 | h1481
      · linarith only [h0, h1481, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1483 | h1483
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1484 | h1484
          · linarith only [h0, h1479, h1484, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1486 | h1486
            · linarith only [h1, h1486, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1488 | h1488
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1489 | h1489
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1490 | h1490
                  · linarith only [h0, h1481, h1490, h2, hlam]
                  · linarith only [h0, h1488, h1490, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h1480, h1488, h1489, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1479, h1481, h1488, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1495 | h1495
          · linarith only [h0, h1480, h1483, h1495, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1497 | h1497
            · linarith only [h0, h1480, h1497, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1499 | h1499
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1500 | h1500
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1501 | h1501
                  · linarith only [h0, h1481, h1501, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1501, h2, hc12, hlam, hphi, u2elo4]
                · linarith only [h1480, h1481, h1499, h1500, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1479, h1481, h1499, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1506 | h1506
      · linarith only [h0, h1480, h1506, h2, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1508 | h1508
        · linarith only [h1479, h1480, h1508, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1510 | h1510
          · linarith only [h1, h1479, h1480, h1510, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1512 | h1512
            · linarith only [h1, h1512, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1514 | h1514
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1515 | h1515
                · linarith only [h0, h1480, h1515, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1517 | h1517
                  · linarith only [h0, h1506, h1517, hlam]
                  · linarith only [h1, h1514, h1515, h1517, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1479, h1480, h1514, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1521 | h1521
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1522 | h1522
      · linarith only [h0, h1479, h1522, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1524 | h1524
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1525 | h1525
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
            · linarith only [h0, h1479, h1521, h1526, h2, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
              · linarith only [h0, h1479, h1528, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1530 | h1530
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1531 | h1531
                  · linarith only [h0, h1522, h1531, hlam]
                  · linarith only [h0, h1530, h1531, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1479, h1521, h1530, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1535 | h1535
            · linarith only [h0, h1479, h1521, h1535, h2, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1537 | h1537
              · linarith only [h0, h1479, h1537, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1539 | h1539
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1540 | h1540
                  · linarith only [h0, h1522, h1540, h2, hlam]
                  · linarith only [h0, h1539, h1540, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1479, h1521, h1539, hc12, hlam, hphi, u2elo2]
        · linarith only [h1479, h1521, h1524, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1545 | h1545
      · linarith only [h0, h1479, h1545, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1547 | h1547
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1548 | h1548
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1549 | h1549
            · linarith only [h1, h1549, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1551 | h1551
              · linarith only [h1479, h1551, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1553 | h1553
                · linarith only [h0, h1521, h1553, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1555 | h1555
                  · linarith only [h1, h1545, h1553, h1555, h2, hlam]
                  · linarith only [h1, h1553, h1555, h2, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1558 | h1558
            · linarith only [h1, h1558, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1560 | h1560
              · linarith only [h0, h1479, h1547, h1560, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1562 | h1562
                · linarith only [h0, h1521, h1562, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1564 | h1564
                  · linarith only [h0, h1479, h1545, h1564, h2, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1, h1562, h1564, h2, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1567 | h1567
          · linarith only [h1, h1547, h1567, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1569 | h1569
            · linarith only [h1, h1569, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1571 | h1571
              · linarith only [h0, h1479, h1571, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1573 | h1573
                · linarith only [h0, h1521, h1573, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1575 | h1575
                  · linarith only [h0, h1545, h1575, h2, hlam]
                  · linarith only [h1, h1573, h1575, h2, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2

end R2N4
