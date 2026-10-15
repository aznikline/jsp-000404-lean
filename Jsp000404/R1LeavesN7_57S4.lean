import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_57S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3892000 in
set_option maxHeartbeats 3892000 in
theorem r1l7_20_11_13_14_H_L_L_0_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h713 | h713
  · rcases m.htr 0 1 4 (by decide) (by decide) with h714 | h714
    · rcases m.htr 0 2 3 (by decide) (by decide) with h715 | h715
      · rcases m.htr 0 2 4 (by decide) (by decide) with h716 | h716
        · rcases m.htr 0 2 5 (by decide) (by decide) with h717 | h717
          · rcases m.htr 0 3 4 (by decide) (by decide) with h718 | h718
            · rcases m.htr 0 3 5 (by decide) (by decide) with h719 | h719
              · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
                · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h723 | h723
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h724 | h724
                        · linarith only [h713, h724, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h713, h718, h724, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h717, h723, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h713, h716, h721, h722, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h715, h721, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
                        · linarith only [h713, h733, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h718, h733, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h717, h732, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h713, h716, h730, h731, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h715, h730, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
                · linarith only [h718, h719, h739, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h744 | h744
                        · linarith only [h713, h744, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h718, h744, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h717, h743, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h713, h716, h741, h742, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h715, h741, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
              · rcases m.htr 0 4 5 (by decide) (by decide) with h751 | h751
                · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h753 | h753
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                        · linarith only [h713, h718, h755, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h757 | h757
                          · linarith only [h0, h714, h755, h757, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h750, h757, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h717, h754, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h713, h716, h752, h753, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h715, h752, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h718, h750, h751, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h764 | h764
                · rcases m.htr 1 2 3 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h767 | h767
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h768 | h768
                        · linarith only [h713, h718, h768, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h770 | h770
                          · linarith only [h713, h750, h770, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h772 | h772
                            · linarith only [h0, h714, h772, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h764, h772, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h717, h767, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h713, h716, h765, h766, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h715, h765, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h780 | h780
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h781 | h781
                        · linarith only [h713, h718, h781, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h783 | h783
                          · linarith only [h0, h714, h750, h764, h781, h783, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                            · linarith only [h714, h764, h785, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h787 | h787
                              · linarith only [h713, h718, h778, h787, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h789 | h789
                                · linarith only [h713, h750, h778, h789, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
                                  · linarith only [h714, h764, h779, h791, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h793 | h793
                                    · rcases h3bigk with h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h778, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p794_1, u0elo2]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h0, h713, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p794_1, u1elo1]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h718, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h750, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h713, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h0, h713, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p794_1, u1elo1]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h781, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h783, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h715, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h778, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h787, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h789, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        rcases p794_3 (m.d 0 3) (by simp) with h810 | h810
                                        · linarith only [h810, hlam, p794_0]
                                        · rcases p794_3 (m.d 1 3) (by simp) with h812 | h812
                                          · linarith only [h781, h812, hlam]
                                          · rcases p794_3 (m.d 2 3) (by simp) with h814 | h814
                                            · linarith only [h787, h814, hlam]
                                            · rcases p794_3 (m.d 3 4) (by simp) with h816 | h816
                                              · rcases p794_3 (m.d 3 5) (by simp) with h817 | h817
                                                · linarith only [h793, h817, hlam]
                                                · linarith only [h750, h817, hlam]
                                              · linarith only [h816, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        rcases p794_3 (m.d 0 3) (by simp) with h821 | h821
                                        · linarith only [h718, h821, hlam]
                                        · linarith only [h713, h821, hlam]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        rcases p794_3 (m.d 0 3) (by simp) with h824 | h824
                                        · linarith only [h718, h824, hlam]
                                        · linarith only [h715, h824, hlam]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h718, h764, h793, hc03, hc34, hlam, hphi, p794_1]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        rcases p794_3 (m.d 0 3) (by simp) with h829 | h829
                                        · linarith only [h829, hlam, p794_0]
                                        · rcases p794_3 (m.d 1 3) (by simp) with h831 | h831
                                          · linarith only [h783, h831, hlam]
                                          · rcases p794_3 (m.d 2 3) (by simp) with h833 | h833
                                            · linarith only [h789, h833, hlam]
                                            · rcases p794_3 (m.d 3 4) (by simp) with h835 | h835
                                              · rcases p794_3 (m.d 3 5) (by simp) with h836 | h836
                                                · rcases h4bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h778, h781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u0elo3]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h0, h714, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p837_1, u1elo1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h718, hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h764, hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h714, hlam, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h0, h714, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p837_1, u1elo1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h781, hlam, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h785, hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h716, hlam, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h779, hlam, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h787, hlam, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h791, hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    rcases p837_3 (m.d 0 4) (by simp) with h853 | h853
                                                    · linarith only [h718, h853, hlam]
                                                    · rcases p837_3 (m.d 1 4) (by simp) with h855 | h855
                                                      · linarith only [h781, h855, hlam]
                                                      · rcases p837_3 (m.d 2 4) (by simp) with h857 | h857
                                                        · linarith only [h787, h857, hlam]
                                                        · rcases p837_3 (m.d 3 4) (by simp) with h859 | h859
                                                          · rcases p837_3 (m.d 4 5) (by simp) with h860 | h860
                                                            · linarith only [h793, h860, hlam]
                                                            · linarith only [h764, h860, hlam]
                                                          · linarith only [h718, h859, hlam]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    rcases p837_3 (m.d 0 4) (by simp) with h864 | h864
                                                    · linarith only [h718, h864, hlam]
                                                    · linarith only [h714, h864, hlam]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    rcases p837_3 (m.d 0 4) (by simp) with h867 | h867
                                                    · linarith only [h718, h867, hlam]
                                                    · linarith only [h716, h867, hlam]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h714, h764, h778, h781, hc23, hc34, hlam, hphi, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h714, h778, h781, h793, hc23, hc34, hlam, hphi, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h778, h781, h793, hc23, hc34, hlam, hphi, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h787, h793, hc23, hc34, hlam, hphi, p837_1]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [h793, hlam, p837_0]
                                                  · have p837_0 := h837c.1
                                                    have p837_1 := h837c.2.1
                                                    have p837_2 := h837c.2.2.1
                                                    have p837_3 := h837c.2.2.2
                                                    linarith only [hlam, p837_0]
                                                · linarith only [h836, hlam, p794_0]
                                              · linarith only [h718, h835, hlam]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        rcases p794_3 (m.d 0 3) (by simp) with h879 | h879
                                        · linarith only [h750, h879, hlam]
                                        · linarith only [h713, h879, hlam]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        rcases p794_3 (m.d 0 3) (by simp) with h882 | h882
                                        · linarith only [h750, h882, hlam]
                                        · linarith only [h715, h882, hlam]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [h793, hlam, p794_0]
                                      · have p794_0 := h794c.1
                                        have p794_1 := h794c.2.1
                                        have p794_2 := h794c.2.2.1
                                        have p794_3 := h794c.2.2.2
                                        linarith only [hlam, p794_0]
                                    · rcases h3bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h778, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p887_1, u0elo2]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h0, h713, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p887_1, u1elo1]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h718, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h750, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h713, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h714, h781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p887_1, u0elo3]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h781, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h783, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h715, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h778, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h787, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h789, hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h793, hc03, hc45, hlam, hphi, ht34, p887_1]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h793, hc13, hc45, hlam, hphi, ht34, p887_1]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h793, hc23, hc45, hlam, hphi, ht34, p887_1]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [hlam, p887_0]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h793, hlam, p887_1]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        rcases p887_3 (m.d 0 3) (by simp) with h908 | h908
                                        · linarith only [h908, hlam, p887_0]
                                        · rcases p887_3 (m.d 1 3) (by simp) with h910 | h910
                                          · linarith only [h783, h910, hlam]
                                          · rcases p887_3 (m.d 2 3) (by simp) with h912 | h912
                                            · linarith only [h789, h912, hlam]
                                            · rcases p887_3 (m.d 3 4) (by simp) with h914 | h914
                                              · linarith only [h793, h914, hlam]
                                              · linarith only [h718, h914, hlam]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        rcases p887_3 (m.d 0 3) (by simp) with h917 | h917
                                        · linarith only [h750, h917, hlam]
                                        · linarith only [h713, h917, hlam]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        rcases p887_3 (m.d 0 3) (by simp) with h920 | h920
                                        · linarith only [h750, h920, hlam]
                                        · linarith only [h715, h920, hlam]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [h713, h718, h778, h793, hc23, hc45, hlam, hphi, ht34, p887_1]
                                      · have p887_0 := h887c.1
                                        have p887_1 := h887c.2.1
                                        have p887_2 := h887c.2.2.1
                                        have p887_3 := h887c.2.2.2
                                        linarith only [hlam, p887_0]
                      · linarith only [h0, h717, h780, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h713, h716, h778, h779, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h715, h778, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h928 | h928
            · rcases m.htr 0 3 5 (by decide) (by decide) with h929 | h929
              · linarith only [h0, h713, h717, h929, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h931 | h931
                · linarith only [h0, h713, h717, h928, h931, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h933 | h933
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h934 | h934
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h935 | h935
                      · linarith only [h0, h717, h935, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h937 | h937
                        · linarith only [h713, h937, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h713, h717, h928, h937, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h716, h717, h934, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h713, h715, h717, h933, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h942 | h942
              · linarith only [h0, h714, h717, h928, h942, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h944 | h944
                · linarith only [h0, h714, h717, h944, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h947 | h947
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h948 | h948
                      · linarith only [h0, h713, h717, h946, h948, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                        · linarith only [h713, h928, h950, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h952 | h952
                          · linarith only [h0, h713, h717, h942, h952, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h954 | h954
                            · linarith only [h714, h928, h944, h954, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h956 | h956
                              · linarith only [h713, h928, h946, h956, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h958 | h958
                                · linarith only [h0, h713, h717, h946, h952, h958, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                                · linarith only [h0, h714, h947, h948, h956, h958, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h713, h716, h717, h946, h947, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h715, h717, h946, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h714, h716, hlam]
      · linarith only [h0, h713, h715, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h965 | h965
      · rcases m.htr 0 2 4 (by decide) (by decide) with h966 | h966
        · rcases m.htr 0 2 5 (by decide) (by decide) with h967 | h967
          · rcases m.htr 0 3 4 (by decide) (by decide) with h968 | h968
            · linarith only [h713, h714, h968, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h970 | h970
              · rcases m.htr 0 4 5 (by decide) (by decide) with h971 | h971
                · rcases m.htr 1 2 3 (by decide) (by decide) with h972 | h972
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h973 | h973
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h974 | h974
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h975 | h975
                        · linarith only [h968, h970, h975, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h977 | h977
                          · linarith only [h713, h714, h966, h977, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h970, h977, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h967, h974, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h966, h973, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h713, h965, h972, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h713, h714, h970, h971, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h984 | h984
                · rcases m.htr 1 2 3 (by decide) (by decide) with h985 | h985
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h986 | h986
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h987 | h987
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h988 | h988
                        · linarith only [h713, h988, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h990 | h990
                          · linarith only [h713, h970, h990, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h992 | h992
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                              · linarith only [h713, h714, h985, h988, h993, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h995 | h995
                                · linarith only [h713, h714, h970, h985, h986, h995, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h997 | h997
                                  · linarith only [h966, h997, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h966, h984, h997, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h714, h966, h984, h992, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h713, h714, h967, h985, h986, h987, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h966, h986, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h965, h985, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1006 | h1006
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
                        · linarith only [h1007, h713, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1009 | h1009
                          · linarith only [h1005, h1009, h713, h714, h970, h984, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
                            · linarith only [h1004, h1005, h1011, h713, h714, h984, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h1004, h1011, h713, h714, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h1006, h967, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1004, h1005, h713, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1004, h713, h965, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1017 | h1017
            · linarith only [h1017, h713, h714, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1019 | h1019
              · linarith only [h0, h1019, h713, h967, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1021 | h1021
                · linarith only [h1021, h966, h967, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1025 | h1025
                      · linarith only [h1025, h714, h966, h967, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1027 | h1027
                        · linarith only [h1027, h713, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1029 | h1029
                          · linarith only [h1019, h1029, h713, h714, h966, h967, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1031 | h1031
                            · linarith only [h1021, h1024, h1025, h1031, h714, hc01, hc25, hlam, hphi, ht12]
                            · linarith only [h1023, h1031, h713, h714, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1024, h966, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1023, h965, h967, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1036 | h1036
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1037 | h1037
            · linarith only [h0, h1037, h713, h966, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1039 | h1039
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1040 | h1040
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1041 | h1041
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1042 | h1042
                    · linarith only [h0, h1041, h1042, h713, h966, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1044 | h1044
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1045 | h1045
                        · linarith only [h1037, h1045, h713, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1047 | h1047
                          · linarith only [h0, h1047, h713, h966, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1039, h1047, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1036, h1044, h966, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1041, h965, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h1039, h1040, h713, h966, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1053 | h1053
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1054 | h1054
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1055 | h1055
                    · linarith only [h0, h1055, h966, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1057 | h1057
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1058 | h1058
                        · linarith only [h1037, h1058, h713, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1060 | h1060
                          · linarith only [h0, h1039, h1060, h713, h966, hc05, hlam, hphi, ht0b, ht5b, u0elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1062 | h1062
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                              · linarith only [h0, h1055, h1058, h1063, h965, h966, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h0, h1054, h1055, h1063, h713, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h1053, h1054, h1055, h1062, h713, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1036, h1054, h1057, h713, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1054, h713, h965, h966, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h1036, h1053, h966, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1070 | h1070
            · linarith only [h0, h1070, h713, h966, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1072 | h1072
              · linarith only [h0, h1036, h1072, h713, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1074 | h1074
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1075 | h1075
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1076 | h1076
                    · linarith only [h0, h1076, h966, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1078 | h1078
                      · linarith only [h0, h1036, h1075, h1078, h713, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1080 | h1080
                        · linarith only [h1070, h1080, h713, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1082 | h1082
                          · linarith only [h0, h1036, h1072, h1082, h713, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1084 | h1084
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1085 | h1085
                              · linarith only [h1075, h1078, h1080, h1084, h1085, h713, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · linarith only [h0, h1075, h1076, h1085, h713, hc23, hc34, hlam, hphi]
                            · linarith only [h1075, h1084, h713, h714, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1036, h1074, h1075, h965, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1090 | h1090
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1091 | h1091
                    · linarith only [h0, h1090, h1091, h713, h966, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1093 | h1093
                      · linarith only [h0, h1036, h1090, h1091, h1093, h713, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1095 | h1095
                        · linarith only [h1095, h713, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1097 | h1097
                          · linarith only [h0, h1072, h1074, h1097, h713, h966, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1099 | h1099
                            · linarith only [h0, h1074, h1099, h966, hc01, hlam, hphi, u1elo3]
                            · linarith only [h1090, h1099, h713, h714, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1090, h713, h965, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h713, h965, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1104 | h1104
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1105 | h1105
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1106 | h1106
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1107 | h1107
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1108 | h1108
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1109 | h1109
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1110 | h1110
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                            · linarith only [h1104, h1116, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1104, h1105, h1110, h1116, h713, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1105, h1109, h1115, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1104, h1105, h1108, h1112, h1114, h713, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1104, h1107, h1111, h1112, h1113, h713, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h1111, h1112, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1105, h1111, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1128 | h1128
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1129 | h1129
                            · linarith only [h1104, h1110, h1129, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                              · linarith only [h1105, h1131, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1104, h1124, h1127, h1131, h713, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h1105, h1109, h1128, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1105, h1108, h1127, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1104, h1107, h1124, h1125, h1126, h713, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h1124, h1125, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1104, h1105, h1124, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1139 | h1139
                · linarith only [h1104, h1109, h1139, h713, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1141 | h1141
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1142 | h1142
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1143 | h1143
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1144 | h1144
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1145 | h1145
                          · linarith only [h1109, h1141, h1145, h713, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1147 | h1147
                            · linarith only [h1104, h1139, h1145, h1147, h713, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1149 | h1149
                              · linarith only [h1105, h1149, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1108, h1149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1104, h1108, h1142, h1144, h713, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h1107, h1143, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1106, h1141, h1142, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1104, h1105, h1141, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h1104, h1108, h713, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1157 | h1157
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1158 | h1158
              · linarith only [h1105, h1107, h1158, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1160 | h1160
                · linarith only [h0, h1104, h1107, h1160, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1162 | h1162
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1163 | h1163
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1164 | h1164
                      · linarith only [h1105, h1107, h1164, h713, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1166 | h1166
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1167 | h1167
                          · linarith only [h1104, h1158, h1163, h1167, h713, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1169 | h1169
                            · linarith only [h1104, h1160, h1169, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1171 | h1171
                              · linarith only [h1105, h1107, h1171, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h1105, h1107, h1157, h1171, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h1157, h1166, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1106, h1107, h1163, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h1104, h1105, h1107, h1162, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
            · linarith only [h1104, h1157, h713, hlam]
        · linarith only [h0, h1104, h1106, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1179 | h1179
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1180 | h1180
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1181 | h1181
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1182 | h1182
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1183 | h1183
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
                  · linarith only [h0, h1105, h1184, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1187 | h1187
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1188 | h1188
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1189 | h1189
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1190 | h1190
                            · linarith only [h1104, h1190, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1183, h1190, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h0, h1182, h1184, h1189, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1104, h1181, h1184, h1186, h1188, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1104, h1180, h1186, h1187, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1105, h1179, h1186, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
                  · linarith only [h1105, h1179, h1197, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1200 | h1200
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1201 | h1201
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1202 | h1202
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1203 | h1203
                            · linarith only [h1104, h1183, h1203, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1205 | h1205
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1206 | h1206
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1207 | h1207
                                  · linarith only [h0, h1104, h1197, h1199, h1203, h1207, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1209 | h1209
                                    · linarith only [h1105, h1179, h1183, h1205, h1209, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · rcases h3bigk with h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h713, hlam, p1211_1]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1105, hlam, p1211_1]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u0elo2]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1209, hc34, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u0elo2]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1105, h1180, hc25, hlam, hphi, ht01, ht0b, ht5b, p1211_1, u1elo2]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1197, hlam, p1211_1]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        rcases p1211_3 (m.d 0 3) (by simp) with h1220 | h1220
                                        · linarith only [h1220, h713, hlam]
                                        · linarith only [h1181, h1220, hlam]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        rcases p1211_3 (m.d 0 3) (by simp) with h1223 | h1223
                                        · linarith only [h1223, h713, hlam]
                                        · linarith only [h1182, h1223, hlam]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        rcases p1211_3 (m.d 0 3) (by simp) with h1226 | h1226
                                        · linarith only [h1105, h1226, hlam]
                                        · rcases p1211_3 (m.d 1 3) (by simp) with h1228 | h1228
                                          · linarith only [h1197, h1228, hlam]
                                          · linarith only [h1228, h713, hlam]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1104, h1199, h1205, h713, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1211_1]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h0, h1104, h1197, h1199, h1205, hlam, p1211_2]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        rcases p1211_3 (m.d 0 3) (by simp) with h1234 | h1234
                                        · linarith only [h1105, h1234, hlam]
                                        · linarith only [h1182, h1234, hlam]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1181, hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1201, hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1205, hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1209, hlam, p1211_1]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1182, hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1202, hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1206, hlam, p1211_0]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [h1180, h1206, hc34, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u0elo1]
                                      · have p1211_0 := h1211c.1
                                        have p1211_1 := h1211c.2.1
                                        have p1211_2 := h1211c.2.2.1
                                        have p1211_3 := h1211c.2.2.2
                                        linarith only [hlam, p1211_0]
                                · linarith only [h0, h1104, h1197, h1199, h1202, h1205, h1206, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                              · linarith only [h0, h1104, h1197, h1199, h1205, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1104, h1182, h1197, h1199, h1202, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1104, h1181, h1197, h1199, h1201, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1104, h1105, h1180, h1199, h1200, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1105, h1179, h1199, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1105, h1180, h1182, hlam]
            · linarith only [h0, h1104, h1105, h1181, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1255 | h1255
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1256 | h1256
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1257 | h1257
                · linarith only [h0, h1104, h1180, h1257, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1259 | h1259
                  · linarith only [h0, h1105, h1259, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1261 | h1261
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1262 | h1262
                      · linarith only [h0, h1104, h1180, h1259, h1261, h1262, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1264 | h1264
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1265 | h1265
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1266 | h1266
                            · linarith only [h1104, h1257, h1266, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1268 | h1268
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1269 | h1269
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1270 | h1270
                                  · linarith only [h0, h1179, h1180, h1256, h1262, h1266, h1270, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h0, h1104, h1261, h1262, h1268, h1270, hc34, hc45, hlam, hphi]
                                · linarith only [h1256, h1269, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1104, h1259, h1261, h1268, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1256, h1265, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1104, h1255, h1259, h1261, h1264, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1179, h1180, h1256, h1261, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1278 | h1278
                · linarith only [h0, h1104, h1105, h1256, h1278, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1280 | h1280
                  · linarith only [h0, h1105, h1280, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1282 | h1282
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1283 | h1283
                      · linarith only [h0, h1104, h1180, h1280, h1282, h1283, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1285 | h1285
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1286 | h1286
                          · linarith only [h0, h1104, h1105, h1256, h1282, h1286, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1288 | h1288
                            · linarith only [h1104, h1278, h1288, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1290 | h1290
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1291 | h1291
                                · linarith only [h0, h1280, h1286, h1291, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h1104, h1280, h1282, h1290, h1291, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h1280, h1290, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1104, h1255, h1280, h1282, h1285, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1179, h1282, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1104, h1105, h1255, hlam]
        · linarith only [h0, h1104, h1179, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1299 | h1299
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1300 | h1300
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1301 | h1301
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1302 | h1302
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1303 | h1303
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1304 | h1304
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1305 | h1305
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1306 | h1306
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1307 | h1307
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1308 | h1308
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1309 | h1309
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1310 | h1310
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1311 | h1311
                              · linarith only [h1299, h1311, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1299, h1302, h1311, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1104, h1299, h1302, h1304, h1310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1299, h1303, h1309, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1302, h1308, h713, hlam]
                      · linarith only [h1301, h1307, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1300, h1306, hlam]
                  · linarith only [h0, h1299, h1305, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1320 | h1320
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1321 | h1321
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1322 | h1322
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1323 | h1323
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1324 | h1324
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1325 | h1325
                            · linarith only [h1104, h1304, h1325, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1327 | h1327
                              · linarith only [h1299, h1327, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1302, h1327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1299, h1303, h1324, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1302, h1323, h713, hlam]
                      · linarith only [h0, h1301, h1322, hlam]
                    · linarith only [h0, h1300, h1321, hlam]
                  · linarith only [h0, h1299, h1320, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1335 | h1335
                · linarith only [h1302, h1303, h1335, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1337 | h1337
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1338 | h1338
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1339 | h1339
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1340 | h1340
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1341 | h1341
                          · linarith only [h1303, h1337, h1341, h713, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1343 | h1343
                            · linarith only [h1104, h1335, h1343, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1345 | h1345
                              · linarith only [h1299, h1345, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1302, h1345, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1301, h1302, h1303, h1340, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1301, h1339, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1300, h1301, h1338, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h0, h1299, h1337, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1352 | h1352
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1353 | h1353
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1355 | h1355
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1356 | h1356
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1357 | h1357
                        · linarith only [h1302, h1352, h1357, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1359 | h1359
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1360 | h1360
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1361 | h1361
                              · linarith only [h1299, h1357, h1361, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1363 | h1363
                                · linarith only [h1300, h1361, h1363, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h1352, h1363, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1104, h1353, h1360, hlam]
                          · linarith only [h1352, h1359, h713, hlam]
                      · linarith only [h0, h1301, h1356, hlam]
                    · linarith only [h0, h1300, h1355, hlam]
                  · linarith only [h0, h1299, h1354, hlam]
                · linarith only [h1302, h1352, h1353, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1372 | h1372
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1374 | h1374
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1375 | h1375
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1376 | h1376
                        · linarith only [h1302, h1376, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1378 | h1378
                          · linarith only [h1352, h1374, h1376, h1378, h713, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1380 | h1380
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1381 | h1381
                              · linarith only [h1299, h1376, h1381, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1383 | h1383
                                · linarith only [h1299, h1378, h1383, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1385 | h1385
                                  · linarith only [h1300, h1385, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h1300, h1372, h1381, h1385, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1300, h1372, h1380, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1301, h1375, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1300, h1374, hlam]
                  · linarith only [h0, h1299, h1373, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1392 | h1392
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1393 | h1393
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1395 | h1395
                        · linarith only [h1302, h1395, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1397 | h1397
                          · linarith only [h1352, h1393, h1395, h1397, h713, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
                            · linarith only [h1104, h1372, h1393, h1399, hc01, hlam, hphi, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1401 | h1401
                              · linarith only [h1299, h1395, h1401, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1403 | h1403
                                · linarith only [h1300, h1397, h1401, h1403, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1405 | h1405
                                  · linarith only [h1300, h1399, h1405, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1407 | h1407
                                    · linarith only [h1395, h1399, h1407, h713, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1395, h1407, h713, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h1301, h1394, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1300, h1393, hlam]
                  · linarith only [h0, h1299, h1392, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1413 | h1413
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1414 | h1414
              · linarith only [h1299, h1301, h1414, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1416 | h1416
                · linarith only [h1299, h1301, h1413, h1416, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1418 | h1418
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1419 | h1419
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1420 | h1420
                      · linarith only [h1299, h1301, h1420, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1422 | h1422
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1423 | h1423
                          · linarith only [h1414, h1423, h713, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1425 | h1425
                            · linarith only [h1104, h1416, h1425, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1427 | h1427
                              · linarith only [h1299, h1427, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1413, h1427, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1299, h1301, h1413, h1422, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h1300, h1301, h1419, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h1299, h1301, h1418, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1433 | h1433
              · linarith only [h1299, h1301, h1433, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1435 | h1435
                · linarith only [h1300, h1301, h1435, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1437 | h1437
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1438 | h1438
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1439 | h1439
                      · linarith only [h1299, h1301, h1439, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1441 | h1441
                        · linarith only [h1413, h1441, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1443 | h1443
                          · linarith only [h1433, h1441, h1443, h713, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1445 | h1445
                            · linarith only [h1104, h1435, h1438, h1439, h1445, hc01, hc25, hlam, hphi, ht12]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1447 | h1447
                              · linarith only [h1299, h1447, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1449 | h1449
                                · linarith only [h1299, h1443, h1449, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1451 | h1451
                                  · linarith only [h1300, h1301, h1451, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1453 | h1453
                                    · linarith only [h0, h1439, h1451, h1453, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1441, h1453, h713, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1300, h1301, h1438, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h1299, h1301, h1437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1458 | h1458
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1459 | h1459
            · linarith only [h1299, h1300, h1459, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1461 | h1461
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1462 | h1462
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1463 | h1463
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1464 | h1464
                    · linarith only [h1299, h1300, h1464, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1466 | h1466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1467 | h1467
                        · linarith only [h1459, h1461, h1467, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1469 | h1469
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1471 | h1471
                              · linarith only [h1299, h1467, h1471, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                                · linarith only [h1299, h1300, h1473, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                                · linarith only [h1461, h1473, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1104, h1462, h1470, hlam]
                          · linarith only [h1461, h1469, h713, hlam]
                      · linarith only [h0, h1458, h1466, hlam]
                  · linarith only [h0, h1299, h1463, hlam]
                · linarith only [h1299, h1300, h1461, h1462, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1481 | h1481
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1482 | h1482
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1483 | h1483
                    · linarith only [h1299, h1300, h1483, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1486 | h1486
                        · linarith only [h1459, h1486, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1488 | h1488
                          · linarith only [h1461, h1486, h1488, h713, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1490 | h1490
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1491 | h1491
                              · linarith only [h1299, h1491, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1493 | h1493
                                · linarith only [h1299, h1488, h1493, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1495 | h1495
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1496 | h1496
                                    · rcases h3bigk with h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h713, hlam, p1497_1]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1300, h1458, h1461, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1497_1, u0elo3]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1459, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1461, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1488, hc03, hc35, hlam, hphi, p1497_1]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1482, h1483, h1491, hc23, hc34, hlam, hphi, p1497_1]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1486, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1488, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1299, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1482, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1491, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1493, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        rcases p1497_3 (m.d 0 3) (by simp) with h1513 | h1513
                                        · linarith only [h1513, hlam, p1497_0]
                                        · rcases p1497_3 (m.d 1 3) (by simp) with h1515 | h1515
                                          · linarith only [h1486, h1515, hlam]
                                          · linarith only [h1515, h713, hlam]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h713, hc01, hc34, hlam, hphi, ht12, ht23, p1497_1]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        rcases p1497_3 (m.d 0 3) (by simp) with h1519 | h1519
                                        · linarith only [h1459, h1519, hlam]
                                        · linarith only [h1299, h1519, hlam]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1461, h713, hc01, hc34, hlam, hphi, ht12, ht23, p1497_1]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        rcases p1497_3 (m.d 0 3) (by simp) with h1524 | h1524
                                        · linarith only [h1524, hlam, p1497_0]
                                        · rcases p1497_3 (m.d 1 3) (by simp) with h1526 | h1526
                                          · linarith only [h1488, h1526, hlam]
                                          · linarith only [h1526, h713, hlam]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h713, hc01, hc35, hlam, hphi, ht12, ht23, p1497_1]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        rcases p1497_3 (m.d 0 3) (by simp) with h1530 | h1530
                                        · linarith only [h1461, h1530, hlam]
                                        · linarith only [h1299, h1530, hlam]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [h1496, hlam, p1497_0]
                                      · have p1497_0 := h1497c.1
                                        have p1497_1 := h1497c.2.1
                                        have p1497_2 := h1497c.2.2.1
                                        have p1497_3 := h1497c.2.2.2
                                        linarith only [hlam, p1497_0]
                                    · linarith only [h1300, h1458, h1483, h1491, h1495, h1496, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                  · linarith only [h1483, h1485, h1488, h1495, h713, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h1104, h1481, h1490, hlam]
                      · linarith only [h0, h1458, h1485, hlam]
                  · linarith only [h0, h1299, h1482, hlam]
                · linarith only [h1300, h1458, h1481, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1541 | h1541
            · linarith only [h1299, h1300, h1541, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1543 | h1543
              · linarith only [h1299, h1458, h1543, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1545 | h1545
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1546 | h1546
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1547 | h1547
                    · linarith only [h1299, h1300, h1547, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1549 | h1549
                      · linarith only [h1299, h1458, h1547, h1549, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1551 | h1551
                        · linarith only [h1541, h1551, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1553 | h1553
                          · linarith only [h1543, h1551, h1553, h713, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1555 | h1555
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1556 | h1556
                              · linarith only [h1299, h1556, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1558 | h1558
                                · linarith only [h1299, h1553, h1558, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1560 | h1560
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1561 | h1561
                                    · rcases h3bigk with h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h713, hlam, p1562_1]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1299, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1562_1, u0elo1]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1541, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1543, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h713, hc01, hlam, hphi, p1562_1, u1elo2]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1546, h1549, h1556, h1560, hc23, hc34, hlam, hphi, p1562_1]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1551, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1553, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1299, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1546, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1556, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1558, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        rcases p1562_3 (m.d 0 3) (by simp) with h1578 | h1578
                                        · linarith only [h1578, hlam, p1562_0]
                                        · rcases p1562_3 (m.d 1 3) (by simp) with h1580 | h1580
                                          · linarith only [h1551, h1580, hlam]
                                          · linarith only [h1580, h713, hlam]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h713, hc01, hc34, hlam, hphi, ht12, ht23, p1562_1]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        rcases p1562_3 (m.d 0 3) (by simp) with h1584 | h1584
                                        · linarith only [h1541, h1584, hlam]
                                        · linarith only [h1299, h1584, hlam]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1549, h1558, hc12, hc34, hlam, hphi, ht23, p1562_1]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        rcases p1562_3 (m.d 0 3) (by simp) with h1589 | h1589
                                        · linarith only [h1589, hlam, p1562_0]
                                        · rcases p1562_3 (m.d 1 3) (by simp) with h1591 | h1591
                                          · linarith only [h1553, h1591, hlam]
                                          · linarith only [h1591, h713, hlam]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h713, hc01, hc35, hlam, hphi, ht12, ht23, p1562_1]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        rcases p1562_3 (m.d 0 3) (by simp) with h1595 | h1595
                                        · linarith only [h1543, h1595, hlam]
                                        · linarith only [h1299, h1595, hlam]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [h1561, hlam, p1562_0]
                                      · have p1562_0 := h1562c.1
                                        have p1562_1 := h1562c.2.1
                                        have p1562_2 := h1562c.2.2.1
                                        have p1562_3 := h1562c.2.2.2
                                        linarith only [hlam, p1562_0]
                                    · linarith only [h1545, h1556, h1561, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h1545, h1546, h1547, h1560, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h1104, h1545, h1555, hlam]
                  · linarith only [h1299, h1546, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1604 | h1604
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1605 | h1605
                    · linarith only [h0, h1300, h1605, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1607 | h1607
                      · linarith only [h1299, h1458, h1605, h1607, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1609 | h1609
                        · linarith only [h1541, h1609, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1611 | h1611
                          · linarith only [h1543, h1609, h1611, h713, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1613 | h1613
                            · linarith only [h1104, h1545, h1613, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1615 | h1615
                              · linarith only [h1299, h1615, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1617 | h1617
                                · linarith only [h1299, h1611, h1617, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1619 | h1619
                                  · linarith only [h0, h1605, h1613, h1615, h1619, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h1299, h1300, h1619, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1299, h1604, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1623 | h1623
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1624 | h1624
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1625 | h1625
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1626 | h1626
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1627 | h1627
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1628 | h1628
                  · linarith only [h1299, h1623, h1628, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1630 | h1630
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1631 | h1631
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1632 | h1632
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1633 | h1633
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1634 | h1634
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1635 | h1635
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1636 | h1636
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1637 | h1637
                                  · linarith only [h1299, h1623, h1637, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h1299, h1623, h1627, h1637, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h1104, h1628, h1630, h1636, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h1104, h1628, h1630, h1635, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1104, h1299, h1623, h1627, h1634, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1626, h1628, h1633, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1104, h1625, h1628, h1630, h1632, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1104, h1624, h1630, h1631, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1623, h1630, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1647 | h1647
                  · linarith only [h1299, h1623, h1647, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1649 | h1649
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1650 | h1650
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1651 | h1651
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1652 | h1652
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1653 | h1653
                            · linarith only [h1104, h1627, h1653, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1655 | h1655
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1656 | h1656
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1657 | h1657
                                  · linarith only [h1623, h1653, h1657, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1659 | h1659
                                    · linarith only [h1104, h1624, h1653, h1655, h1657, h1659, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                    · rcases h3bigk with h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h713, hlam, p1661_1]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1299, hlam, p1661_1]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p1661_1, u0elo2]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p1661_1, u0elo2]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1299, h1624, h1657, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1661_1, u1elo2]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1647, hlam, p1661_1]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        rcases p1661_3 (m.d 0 3) (by simp) with h1670 | h1670
                                        · linarith only [h1670, h713, hlam]
                                        · linarith only [h1625, h1670, hlam]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        rcases p1661_3 (m.d 0 3) (by simp) with h1673 | h1673
                                        · linarith only [h1673, h713, hlam]
                                        · linarith only [h1626, h1673, hlam]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        rcases p1661_3 (m.d 0 3) (by simp) with h1676 | h1676
                                        · linarith only [h1299, h1676, hlam]
                                        · rcases p1661_3 (m.d 1 3) (by simp) with h1678 | h1678
                                          · linarith only [h1647, h1678, hlam]
                                          · linarith only [h1678, h713, hlam]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h713, hc01, hc23, hlam, hphi, ht12, p1661_1]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        rcases p1661_3 (m.d 0 3) (by simp) with h1683 | h1683
                                        · linarith only [h1299, h1683, hlam]
                                        · linarith only [h1625, h1683, hlam]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        rcases p1661_3 (m.d 0 3) (by simp) with h1686 | h1686
                                        · linarith only [h1299, h1686, hlam]
                                        · linarith only [h1626, h1686, hlam]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1625, hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1651, hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1655, hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1659, hlam, p1661_1]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1626, hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1652, hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1656, hlam, p1661_0]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [h1626, hc34, hlam, hphi, ht0b, ht45, ht5b, p1661_1, u0elo2]
                                      · have p1661_0 := h1661c.1
                                        have p1661_1 := h1661c.2.1
                                        have p1661_2 := h1661c.2.2.1
                                        have p1661_3 := h1661c.2.2.2
                                        linarith only [hlam, p1661_0]
                                · linarith only [h1626, h1647, h1656, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1104, h1647, h1650, h1653, h1655, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1626, h1652, h713, hlam]
                        · linarith only [h1625, h1626, h1651, h713, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h1624, h1650, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1623, h1649, hlam]
              · linarith only [h1299, h1624, h1626, hlam]
            · linarith only [h1299, h1623, h1625, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1707 | h1707
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1708 | h1708
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1709 | h1709
                · linarith only [h1623, h1624, h1709, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1711 | h1711
                  · linarith only [h1299, h1623, h1711, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1713 | h1713
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1714 | h1714
                      · linarith only [h1623, h1624, h1711, h1714, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1716 | h1716
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1717 | h1717
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1718 | h1718
                            · linarith only [h1104, h1709, h1718, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1720 | h1720
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1721 | h1721
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1722 | h1722
                                  · linarith only [h1623, h1718, h1722, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1724 | h1724
                                    · linarith only [h0, h1714, h1722, h1724, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · rcases h3bigk with h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h713, hlam, p1726_1]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1299, hlam, p1726_1]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p1726_1, u0elo2]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p1726_1, u0elo2]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1623, h1624, h1708, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1726_1, u1elo2]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1711, hlam, p1726_1]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        rcases p1726_3 (m.d 0 3) (by simp) with h1735 | h1735
                                        · linarith only [h1735, h713, hlam]
                                        · linarith only [h1707, h1735, hlam]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        rcases p1726_3 (m.d 0 3) (by simp) with h1738 | h1738
                                        · linarith only [h1738, h713, hlam]
                                        · linarith only [h1708, h1738, hlam]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        rcases p1726_3 (m.d 0 3) (by simp) with h1741 | h1741
                                        · linarith only [h1299, h1741, hlam]
                                        · rcases p1726_3 (m.d 1 3) (by simp) with h1743 | h1743
                                          · linarith only [h1711, h1743, hlam]
                                          · linarith only [h1743, h713, hlam]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h713, hc01, hc23, hlam, hphi, ht12, p1726_1]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        rcases p1726_3 (m.d 0 3) (by simp) with h1748 | h1748
                                        · linarith only [h1299, h1748, hlam]
                                        · linarith only [h1707, h1748, hlam]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        rcases p1726_3 (m.d 0 3) (by simp) with h1751 | h1751
                                        · linarith only [h1299, h1751, hlam]
                                        · linarith only [h1708, h1751, hlam]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1707, hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1716, hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1720, hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1724, hlam, p1726_1]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1708, hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1717, hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1721, hlam, p1726_0]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [h1708, hc34, hlam, hphi, ht0b, ht45, ht5b, p1726_1, u0elo2]
                                      · have p1726_0 := h1726c.1
                                        have p1726_1 := h1726c.2.1
                                        have p1726_2 := h1726c.2.2.1
                                        have p1726_3 := h1726c.2.2.2
                                        linarith only [hlam, p1726_0]
                                · linarith only [h1708, h1721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h1104, h1711, h1713, h1720, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1708, h1717, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1104, h1707, h1711, h1713, h1716, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1623, h1713, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1769 | h1769
                · linarith only [h1299, h1623, h1708, h1769, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1771 | h1771
                  · linarith only [h1299, h1623, h1771, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1773 | h1773
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1774 | h1774
                      · linarith only [h1623, h1624, h1771, h1774, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1776 | h1776
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1777 | h1777
                          · linarith only [h1299, h1623, h1708, h1777, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1779 | h1779
                            · linarith only [h1104, h1769, h1779, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1781 | h1781
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1782 | h1782
                                · linarith only [h0, h1771, h1777, h1782, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1104, h1771, h1773, h1782, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h1104, h1771, h1773, h1781, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1104, h1707, h1708, h1771, h1773, h1776, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1623, h1773, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h1299, h1623, h1707, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1789 | h1789
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1790 | h1790
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1791 | h1791
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1792 | h1792
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1793 | h1793
                  · linarith only [h1299, h1789, h1793, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1795 | h1795
                    · linarith only [h1623, h1789, h1795, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1797 | h1797
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1798 | h1798
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1799 | h1799
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1800 | h1800
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1801 | h1801
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1802 | h1802
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1803 | h1803
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1804 | h1804
                                    · linarith only [h1790, h1804, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                    · linarith only [h1792, h1804, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h1790, h1792, h1795, h1803, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1791, h1802, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1793, h1801, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1790, h1792, h1800, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h1791, h1799, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1790, h1798, h713, hlam]
                      · linarith only [h0, h1789, h1797, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1623, h1789, h1792, hlam]
              · linarith only [h1623, h1789, h1790, h1791, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1816 | h1816
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1817 | h1817
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1818 | h1818
                  · linarith only [h1299, h1789, h1818, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1820 | h1820
                    · linarith only [h1623, h1789, h1820, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1822 | h1822
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1823 | h1823
                        · linarith only [h1790, h1816, h1823, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1825 | h1825
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1826 | h1826
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1827 | h1827
                              · linarith only [h0, h1818, h1823, h1827, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1818, h1827, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1817, h1818, h1823, h1826, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h0, h1816, h1818, h1825, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1789, h1822, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1299, h1789, h1790, h1817, hlam]
              · linarith only [h1299, h1789, h1816, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1835 | h1835
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1836 | h1836
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1838 | h1838
                  · linarith only [h0, h1299, h1838, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1840 | h1840
                    · linarith only [h0, h1623, h1840, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1842 | h1842
                      · linarith only [h0, h1789, h1838, h1842, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1844 | h1844
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1845 | h1845
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1846 | h1846
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1847 | h1847
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1848 | h1848
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1849 | h1849
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1850 | h1850
                                    · linarith only [h1835, h1850, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                    · linarith only [h1837, h1850, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                  · linarith only [h1835, h1837, h1849, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h1836, h1848, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1838, h1847, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1835, h1837, h1846, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h1836, h1845, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1835, h1844, h713, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1859 | h1859
                  · linarith only [h0, h1299, h1859, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1861 | h1861
                    · linarith only [h0, h1623, h1861, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1863 | h1863
                      · linarith only [h0, h1789, h1859, h1863, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1865 | h1865
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1866 | h1866
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1867 | h1867
                            · linarith only [h1104, h1837, h1865, h1867, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1869 | h1869
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1870 | h1870
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1871 | h1871
                                  · linarith only [h0, h1861, h1867, h1871, hc01, hc24, hlam, hphi, ht12]
                                  · linarith only [h0, h1861, h1871, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h1836, h1870, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1835, h1859, h1869, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1836, h1866, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1835, h1865, h713, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1878 | h1878
                · linarith only [h1835, h1836, h1878, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1880 | h1880
                  · linarith only [h0, h1299, h1880, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1882 | h1882
                    · linarith only [h0, h1623, h1882, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1884 | h1884
                      · linarith only [h0, h1789, h1884, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1886 | h1886
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1887 | h1887
                          · linarith only [h1835, h1836, h1887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1889 | h1889
                            · linarith only [h0, h1623, h1878, h1886, h1887, h1889, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1891 | h1891
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1892 | h1892
                                · linarith only [h0, h1882, h1886, h1887, h1892, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h1880, h1892, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h1835, h1880, h1891, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1835, h1886, h713, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1897 | h1897
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1898 | h1898
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1899 | h1899
                  · linarith only [h0, h1299, h1899, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1901 | h1901
                    · linarith only [h0, h1623, h1901, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1903 | h1903
                      · linarith only [h0, h1789, h1899, h1903, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1905 | h1905
                        · linarith only [h1835, h1897, h1905, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1907 | h1907
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1908 | h1908
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1909 | h1909
                              · linarith only [h0, h1903, h1905, h1907, h1909, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1899, h1909, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h1898, h1903, h1905, h1907, h1908, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1897, h1907, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1835, h1897, h1898, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1915 | h1915
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1916 | h1916
                  · linarith only [h0, h1299, h1916, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1918 | h1918
                    · linarith only [h0, h1623, h1918, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1920 | h1920
                      · linarith only [h0, h1789, h1916, h1920, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1922 | h1922
                        · linarith only [h1835, h1922, h713, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1924 | h1924
                          · linarith only [h0, h1299, h1897, h1922, h1924, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1926 | h1926
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1927 | h1927
                              · linarith only [h0, h1916, h1922, h1927, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1916, h1927, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1915, h1926, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1931 | h1931
                  · linarith only [h0, h1299, h1931, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1933 | h1933
                    · linarith only [h0, h1623, h1933, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1935 | h1935
                      · linarith only [h0, h1789, h1931, h1935, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1937 | h1937
                        · linarith only [h0, h1299, h1835, h1937, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1939 | h1939
                          · linarith only [h0, h1299, h1897, h1937, h1939, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1941 | h1941
                            · linarith only [h1104, h1915, h1941, hc01, hlam, hphi, u1elo3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1943 | h1943
                              · linarith only [h0, h1931, h1937, h1943, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1931, h1943, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 3892000 in
set_option maxHeartbeats 3892000 in
theorem r1l7_20_11_13_14_H_L_L_0_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_L_L_0_L_I_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_L_L_0_L_I_L_I_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
