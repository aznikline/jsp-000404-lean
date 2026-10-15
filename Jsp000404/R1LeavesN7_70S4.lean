import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_70S3

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_14_25_L_0_L_I_M_LR_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h711 | h711
  · rcases m.htr 0 3 4 (by decide) (by decide) with h712 | h712
    · rcases m.htr 0 4 5 (by decide) (by decide) with h713 | h713
      · rcases m.htr 1 2 3 (by decide) (by decide) with h714 | h714
        · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
          · rcases m.htr 1 3 4 (by decide) (by decide) with h716 | h716
            · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
              · rcases m.htr 2 3 4 (by decide) (by decide) with h718 | h718
                · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
                  · linarith only [h711, h719, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h721 | h721
                    · linarith only [h718, h719, h721, hlam]
                    · rcases h4bigk with h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h0, hlam, p723_1]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        rcases p723_3 (m.d 0 4) (by simp) with h726 | h726
                        · rcases p723_3 (m.d 1 4) (by simp) with h727 | h727
                          · rcases p723_3 (m.d 2 4) (by simp) with h728 | h728
                            · linarith only [h711, h728, hlam]
                            · rcases p723_3 (m.d 3 4) (by simp) with h730 | h730
                              · linarith only [h712, h730, hlam]
                              · rcases p723_3 (m.d 4 5) (by simp) with h732 | h732
                                · linarith only [h713, h732, hlam]
                                · linarith only [h719, h732, hlam]
                          · linarith only [h715, h727, hlam]
                        · linarith only [h711, h726, hlam]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        rcases p723_3 (m.d 0 4) (by simp) with h737 | h737
                        · rcases p723_3 (m.d 1 4) (by simp) with h738 | h738
                          · rcases p723_3 (m.d 2 4) (by simp) with h739 | h739
                            · linarith only [h711, h739, hlam]
                            · linarith only [h718, h739, hlam]
                          · linarith only [h716, h738, hlam]
                        · linarith only [h712, h737, hlam]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h711, h718, h719, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p723_1, u2elo0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h713, h718, h719, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p723_1]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        rcases p723_3 (m.d 0 4) (by simp) with h747 | h747
                        · linarith only [h0, h747, hlam]
                        · linarith only [h711, h747, hlam]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        rcases p723_3 (m.d 0 4) (by simp) with h750 | h750
                        · linarith only [h0, h750, hlam]
                        · linarith only [h712, h750, hlam]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h714, h716, h718, h719, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p723_1, u2elo1]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h711, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h715, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h712, h713, h719, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p723_1]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h719, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h712, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h716, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h718, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h721, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h713, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h717, hlam, p723_0]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [hc24, hlam, hphi, ht45, p723_1, u5elo4]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [h0, h713, h714, h716, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p723_1, u2elo1]
                      · have p723_0 := h723c.1
                        have p723_1 := h723c.2.1
                        have p723_2 := h723c.2.2.1
                        have p723_3 := h723c.2.2.2
                        linarith only [hlam, p723_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h769 | h769
                  · linarith only [h711, h769, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h771 | h771
                    · linarith only [h714, h716, h769, h771, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h718, h771, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h713, h717, hlam]
            · linarith only [h0, h712, h716, hlam]
          · linarith only [h711, h715, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
          · linarith only [h0, h713, h714, h777, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
          · linarith only [h711, h777, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
        · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
          · rcases m.htr 1 3 4 (by decide) (by decide) with h782 | h782
            · rcases m.htr 1 4 5 (by decide) (by decide) with h783 | h783
              · linarith only [h0, h713, h780, h782, h783, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h783, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h712, h713, h782, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h711, h713, h781, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h788 | h788
          · linarith only [h0, h780, h788, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h711, h788, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h791 | h791
      · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
        · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
          · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
            · linarith only [h712, h791, h792, h794, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
              · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
                · linarith only [h0, h791, h794, h797, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h799 | h799
                  · linarith only [h793, h799, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h801 | h801
                    · rcases h4bigk with h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h0, hlam, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        rcases p802_3 (m.d 0 4) (by simp) with h805 | h805
                        · rcases p802_3 (m.d 1 4) (by simp) with h806 | h806
                          · rcases p802_3 (m.d 2 4) (by simp) with h807 | h807
                            · linarith only [h711, h807, hlam]
                            · rcases p802_3 (m.d 3 4) (by simp) with h809 | h809
                              · rcases p802_3 (m.d 4 5) (by simp) with h810 | h810
                                · linarith only [h791, h810, hlam]
                                · linarith only [h799, h810, hlam]
                              · linarith only [h797, h809, hlam]
                          · linarith only [h793, h806, hlam]
                        · linarith only [h711, h805, hlam]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h712, hlam, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h0, h794, h797, h799, hc23, hc34, hlam, hphi, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h791, h794, h797, h799, hc23, hc34, hlam, hphi, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        rcases p802_3 (m.d 0 4) (by simp) with h820 | h820
                        · linarith only [h0, h820, hlam]
                        · linarith only [h711, h820, hlam]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h794, hlam, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h793, h797, h799, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p802_1, u2elo1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h711, hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h793, hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h797, hlam, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h799, hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h791, h797, h799, hc23, hc34, hlam, hphi, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        rcases p802_3 (m.d 0 4) (by simp) with h832 | h832
                        · linarith only [h712, h832, hlam]
                        · linarith only [h711, h832, hlam]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h797, h799, hc23, hc34, hlam, hphi, p802_1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h791, hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h796, hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h0, h791, h793, h797, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p802_1, u2elo1]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [h801, hlam, p802_0]
                      · have p802_0 := h802c.1
                        have p802_1 := h802c.2.1
                        have p802_2 := h802c.2.2.1
                        have p802_3 := h802c.2.2.2
                        linarith only [hlam, p802_0]
                    · linarith only [h0, h791, h793, h794, h801, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · linarith only [h0, h791, h796, hlam]
          · linarith only [h711, h793, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h845 | h845
          · linarith only [h0, h791, h792, h845, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
          · linarith only [h711, h845, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h848 | h848
        · rcases m.htr 1 2 4 (by decide) (by decide) with h849 | h849
          · rcases m.htr 1 3 4 (by decide) (by decide) with h850 | h850
            · rcases m.htr 1 4 5 (by decide) (by decide) with h851 | h851
              · linarith only [h0, h791, h849, h851, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h854 | h854
              · linarith only [h0, h791, h849, h854, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h854, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · linarith only [h711, h849, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h858 | h858
          · linarith only [h0, h848, h858, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h711, h858, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h861 | h861
    · rcases m.htr 0 4 5 (by decide) (by decide) with h862 | h862
      · rcases m.htr 1 2 3 (by decide) (by decide) with h863 | h863
        · rcases m.htr 1 2 4 (by decide) (by decide) with h864 | h864
          · linarith only [h711, h864, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h866 | h866
            · linarith only [h0, h862, h863, h864, h866, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi9]
            · linarith only [h0, h861, h866, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h869 | h869
          · linarith only [h711, h863, h869, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h871 | h871
            · rcases m.htr 1 4 5 (by decide) (by decide) with h872 | h872
              · rcases m.htr 2 3 4 (by decide) (by decide) with h873 | h873
                · rcases m.htr 2 4 5 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h875 | h875
                    · linarith only [h863, h871, h875, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                    · rcases h4bigk with h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h0, hlam, p877_1]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h711, hlam, p877_1]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        rcases p877_3 (m.d 0 4) (by simp) with h881 | h881
                        · rcases p877_3 (m.d 1 4) (by simp) with h882 | h882
                          · rcases p877_3 (m.d 2 4) (by simp) with h883 | h883
                            · rcases p877_3 (m.d 3 4) (by simp) with h884 | h884
                              · linarith only [h861, h884, hlam]
                              · rcases p877_3 (m.d 4 5) (by simp) with h886 | h886
                                · linarith only [h862, h886, hlam]
                                · linarith only [h875, h886, hlam]
                            · linarith only [h873, h883, hlam]
                          · linarith only [h871, h882, hlam]
                        · linarith only [h861, h881, hlam]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h711, h873, h875, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p877_1, u2elo2]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h862, h875, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p877_1]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h869, hlam, p877_1]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        rcases p877_3 (m.d 0 4) (by simp) with h896 | h896
                        · linarith only [h0, h896, hlam]
                        · linarith only [h861, h896, hlam]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h869, h873, h875, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p877_1, u2elo2]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h862, h873, h875, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p877_1, u2elo2]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h0, h873, hc01, hlam, hphi, ht12, p877_1, u2elo2]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        rcases p877_3 (m.d 0 4) (by simp) with h903 | h903
                        · linarith only [h711, h903, hlam]
                        · linarith only [h861, h903, hlam]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h873, h875, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p877_1, u2elo2]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h861, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h871, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h873, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h875, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h862, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h872, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [h874, hlam, p877_0]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [hc34, hlam, hphi, ht45, p877_1, u5elo4]
                      · have p877_0 := h877c.1
                        have p877_1 := h877c.2.1
                        have p877_2 := h877c.2.2.1
                        have p877_3 := h877c.2.2.2
                        linarith only [hlam, p877_0]
                  · linarith only [h0, h862, h869, h874, hlam]
                · linarith only [h0, h861, h863, h869, h873, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h862, h872, hlam]
            · linarith only [h0, h861, h871, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h921 | h921
        · rcases m.htr 1 2 4 (by decide) (by decide) with h922 | h922
          · linarith only [h711, h922, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h924 | h924
            · linarith only [h0, h921, h922, h924, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h861, h862, h924, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h927 | h927
          · linarith only [h711, h921, h927, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h929 | h929
            · rcases m.htr 1 4 5 (by decide) (by decide) with h930 | h930
              · linarith only [h0, h862, h927, h930, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h930, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h861, h862, h929, hc13, hlam, hphi, ht34, ht45, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h934 | h934
      · rcases m.htr 1 2 3 (by decide) (by decide) with h935 | h935
        · rcases m.htr 1 2 4 (by decide) (by decide) with h936 | h936
          · linarith only [h711, h936, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h938 | h938
            · linarith only [h861, h935, h936, h938, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h940 | h940
              · rcases m.htr 2 3 4 (by decide) (by decide) with h941 | h941
                · linarith only [h0, h934, h938, h941, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h944 | h944
                    · rcases h4bigk with h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h0, hlam, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h711, hlam, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h861, hlam, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h711, hlam, hphi, ht01, ht0b, ht12, ht5b, p945_1, u2elo3, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h934, hc14, hlam, hphi, ht01, ht0b, ht5b, p945_1, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h936, hlam, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h938, hlam, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h936, hlam, hphi, ht01, ht0b, ht12, ht5b, p945_1, u2elo3, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h934, hlam, hphi, ht01, ht0b, ht12, ht5b, p945_1, u2elo3, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht12, p945_1, u2elo3]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h941, hlam, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p945_1, u2elo3, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h934, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h0, h934, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u5ehi9]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h936, hc12, hc34, hlam, hphi, ht23, p945_1]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        rcases p945_3 (m.d 0 4) (by simp) with h965 | h965
                        · linarith only [h861, h965, hlam]
                        · linarith only [h934, h965, hlam]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h934, hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h940, hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h943, hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [h944, hlam, p945_0]
                      · have p945_0 := h945c.1
                        have p945_1 := h945c.2.1
                        have p945_2 := h945c.2.2.1
                        have p945_3 := h945c.2.2.2
                        linarith only [hlam, p945_0]
                    · linarith only [h861, h944, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h934, h936, h943, hlam]
              · linarith only [h0, h934, h940, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h976 | h976
          · linarith only [h711, h935, h976, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
            · linarith only [h861, h934, h935, h978, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h980 | h980
              · rcases m.htr 2 3 4 (by decide) (by decide) with h981 | h981
                · linarith only [h935, h978, h981, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h984 | h984
                    · rcases h4bigk with h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h0, hlam, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h711, hlam, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h861, hlam, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h0, h976, hlam, hphi, ht01, ht0b, ht12, ht5b, p985_1, u2elo3, u5ehi9]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h0, h976, hc01, hlam, hphi, ht12, p985_1, u2elo3]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h976, hlam, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h978, hlam, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h976, hlam, hphi, ht01, ht0b, ht12, ht5b, p985_1, u2elo3, u5ehi9]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h934, hlam, hphi, ht01, ht0b, ht12, ht5b, p985_1, u2elo3, u5ehi9]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht12, p985_1, u2elo3]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h981, hlam, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p985_1, u2elo3, u5ehi9]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h934, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p985_1, u5ehi9]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h0, h934, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p985_1, u5ehi9]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h711, hc02, hc34, hlam, hphi, ht23, p985_1]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        rcases p985_3 (m.d 0 4) (by simp) with h1005 | h1005
                        · linarith only [h1005, h861, hlam]
                        · linarith only [h1005, h934, hlam]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h934, hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h980, hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h983, hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [h984, hlam, p985_0]
                      · have p985_0 := h985c.1
                        have p985_1 := h985c.2.1
                        have p985_2 := h985c.2.2.1
                        have p985_3 := h985c.2.2.2
                        linarith only [hlam, p985_0]
                    · linarith only [h0, h861, h934, h976, h984, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h934, h976, h983, hlam]
              · linarith only [h0, h934, h980, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1016 | h1016
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1017 | h1017
          · linarith only [h1017, h711, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1019 | h1019
            · linarith only [h1016, h1017, h1019, h861, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1021 | h1021
              · linarith only [h0, h1017, h1021, h934, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1021, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
          · linarith only [h1016, h1024, h711, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1027 | h1027
              · linarith only [h0, h1024, h1027, h934, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1016, h1026, h1027, h861, hc01, hc03, hlam, hphi, ht12, ht34, ht45, u2elo2, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1030 | h1030
              · linarith only [h0, h1024, h1030, h934, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h1030, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]

theorem r1l7_12_14_25_L_0_L_I_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_14_25_L_0_L_I_M_LR_x0 m hb2 hb4 hb5 h0
  · exact r1l7_12_14_25_L_0_L_I_M_LR_x1 m hb2 hb4 hb5 h0

end R2N4
