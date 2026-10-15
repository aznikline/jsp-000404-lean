import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h711 | h711
  · rcases m.htr 0 3 4 (by decide) (by decide) with h712 | h712
    · rcases m.htr 0 3 5 (by decide) (by decide) with h713 | h713
      · rcases m.htr 0 4 5 (by decide) (by decide) with h714 | h714
        · rcases m.htr 1 2 3 (by decide) (by decide) with h715 | h715
          · linarith only [h4, h711, h715, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h717 | h717
            · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
              · rcases m.htr 1 3 4 (by decide) (by decide) with h719 | h719
                · rcases m.htr 1 3 5 (by decide) (by decide) with h720 | h720
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h721 | h721
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h722 | h722
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h723 | h723
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h724 | h724
                          · linarith only [h0, h4, h717, h724, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h726 | h726
                            · linarith only [h722, h724, h726, hlam]
                            · rcases h1bigk with h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h717, h721, h722, h724, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h715, h717, h721, h722, h724, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h721, h722, h724, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                rcases p728_3 (m.d 0 1) (by simp) with h733 | h733
                                · rcases p728_3 (m.d 1 2) (by simp) with h734 | h734
                                  · linarith only [h0, h734, hlam]
                                  · linarith only [h718, h734, hlam]
                                · linarith only [h733, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h715, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h721, h722, h724, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p728_1, u5ehi6]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, h717, h722, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, h721, h722, h724, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, h718, h723, hc01, hlam, hphi, ht0b, ht5b, p728_1, u5ehi8]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h2, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h717, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h719, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h717, h718, h723, hc01, hlam, hphi, ht0b, ht5b, p728_1, u5ehi8]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h3, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h718, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h720, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h721, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                        · linarith only [h4, h723, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4, h717, h721, h722, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h760 | h760
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h761 | h761
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h762 | h762
                          · linarith only [h717, h721, h762, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h764 | h764
                            · linarith only [h717, h721, h760, h764, hlam]
                            · rcases h1bigk with h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h718, h761, hc01, hlam, hphi, ht0b, ht5b, p766_1, u5ehi8]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h715, h718, h761, hc01, hlam, hphi, ht0b, ht5b, p766_1, u5ehi8]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h770 | h770
                                · rcases p766_3 (m.d 1 2) (by simp) with h771 | h771
                                  · linarith only [h0, h771, hlam]
                                  · linarith only [h717, h771, hlam]
                                · linarith only [h770, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h775 | h775
                                · rcases p766_3 (m.d 1 2) (by simp) with h776 | h776
                                  · linarith only [h0, h776, hlam]
                                  · linarith only [h718, h776, hlam]
                                · linarith only [h775, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h0, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h715, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h783 | h783
                                · rcases p766_3 (m.d 1 2) (by simp) with h784 | h784
                                  · rcases p766_3 (m.d 1 3) (by simp) with h785 | h785
                                    · rcases p766_3 (m.d 1 4) (by simp) with h786 | h786
                                      · linarith only [h717, h786, hlam]
                                      · rcases p766_3 (m.d 1 5) (by simp) with h788 | h788
                                        · linarith only [h718, h788, hlam]
                                        · linarith only [h721, h788, hlam]
                                    · linarith only [h719, h785, hlam]
                                  · linarith only [h717, h784, hlam]
                                · linarith only [h2, h783, hlam]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h0, h4, h718, h761, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p766_1, u5ehi8]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h1, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h1, h717, h760, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                rcases p766_3 (m.d 0 1) (by simp) with h798 | h798
                                · rcases p766_3 (m.d 1 2) (by simp) with h799 | h799
                                  · linarith only [h715, h799, hlam]
                                  · linarith only [h717, h799, hlam]
                                · linarith only [h2, h798, hlam]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h1, h718, h761, hc01, hlam, hphi, ht0b, ht5b, p766_1, u5ehi8]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h2, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h717, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h719, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h721, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h3, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h718, hlam, p766_1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h720, hlam, p766_0]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [h717, h760, hc34, hlam, hphi, ht45, p766_1, u5elo1]
                              · have p766_0 := h766c.1
                                have p766_1 := h766c.2.1
                                have p766_2 := h766c.2.2.1
                                have p766_3 := h766c.2.2.2
                                linarith only [hlam, p766_0]
                        · linarith only [h4, h761, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4, h718, h760, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h713, h715, h718, h720, hlam, hphi, u5ehi7, u5elo0]
                · linarith only [h712, h715, h718, h719, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h4, h711, h718, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h819 | h819
              · rcases m.htr 1 3 4 (by decide) (by decide) with h820 | h820
                · rcases m.htr 1 3 5 (by decide) (by decide) with h821 | h821
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h822 | h822
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h823 | h823
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h824 | h824
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h825 | h825
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h826 | h826
                            · linarith only [h1, h820, h826, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h1bigk with h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c | h828c
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h819, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h715, h819, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h717, h819, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                rcases p828_3 (m.d 0 1) (by simp) with h833 | h833
                                · rcases p828_3 (m.d 1 2) (by simp) with h834 | h834
                                  · linarith only [h0, h834, hlam]
                                  · linarith only [h819, h834, hlam]
                                · linarith only [h833, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h0, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h715, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h717, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h717, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p828_1, u5ehi6]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h1, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h1, h819, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h1, h717, h819, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h1, h819, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h2, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h2, h819, h825, h826, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h820, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h1, h819, h820, h825, h826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h3, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h819, hlam, p828_1]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h821, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [h822, hlam, p828_0]
                              · have p828_0 := h828c.1
                                have p828_1 := h828c.2.1
                                have p828_2 := h828c.2.2.1
                                have p828_3 := h828c.2.2.2
                                linarith only [hlam, p828_0]
                          · linarith only [h717, h819, h825, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                        · linarith only [h4, h824, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4, h819, h823, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h714, h717, h819, h822, hlam, hphi, u5ehi7, u5elo0]
                  · linarith only [h820, h821, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h712, h715, h819, h820, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h4, h711, h819, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
          · linarith only [h4, h711, h865, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
            · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
              · rcases m.htr 1 3 4 (by decide) (by decide) with h869 | h869
                · rcases m.htr 1 3 5 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h871 | h871
                    · linarith only [h2, h714, h871, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h873 | h873
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h874 | h874
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h875 | h875
                          · linarith only [h2, h714, h867, h875, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h877 | h877
                            · linarith only [h2, h714, h867, h873, h877, hlam]
                            · rcases h1bigk with h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h868, h874, hc01, hlam, hphi, ht0b, ht5b, p879_1, u5ehi8]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h865, h868, h874, hc01, hlam, hphi, ht0b, ht5b, p879_1, u5ehi8]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                rcases p879_3 (m.d 0 1) (by simp) with h883 | h883
                                · rcases p879_3 (m.d 1 2) (by simp) with h884 | h884
                                  · linarith only [h0, h884, hlam]
                                  · linarith only [h867, h884, hlam]
                                · linarith only [h883, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                rcases p879_3 (m.d 0 1) (by simp) with h888 | h888
                                · rcases p879_3 (m.d 1 2) (by simp) with h889 | h889
                                  · linarith only [h0, h889, hlam]
                                  · linarith only [h868, h889, hlam]
                                · linarith only [h888, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h0, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h865, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                rcases p879_3 (m.d 0 1) (by simp) with h896 | h896
                                · rcases p879_3 (m.d 1 2) (by simp) with h897 | h897
                                  · rcases p879_3 (m.d 1 3) (by simp) with h898 | h898
                                    · rcases p879_3 (m.d 1 4) (by simp) with h899 | h899
                                      · linarith only [h867, h899, hlam]
                                      · rcases p879_3 (m.d 1 5) (by simp) with h901 | h901
                                        · linarith only [h868, h901, hlam]
                                        · linarith only [h871, h901, hlam]
                                    · linarith only [h869, h898, hlam]
                                  · linarith only [h867, h897, hlam]
                                · linarith only [h2, h896, hlam]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p879_1, u5ehi6]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h1, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h1, h867, h873, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                rcases p879_3 (m.d 0 1) (by simp) with h911 | h911
                                · rcases p879_3 (m.d 1 2) (by simp) with h912 | h912
                                  · linarith only [h865, h912, hlam]
                                  · linarith only [h867, h912, hlam]
                                · linarith only [h2, h911, hlam]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h1, h868, h874, hc01, hlam, hphi, ht0b, ht5b, p879_1, u5ehi8]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h2, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h867, hlam, p879_1]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h869, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h871, hlam, p879_1]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h3, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h868, hlam, p879_1]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h870, hlam, p879_0]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [h867, h873, hc34, hlam, hphi, ht45, p879_1, u5elo1]
                              · have p879_0 := h879c.1
                                have p879_1 := h879c.2.1
                                have p879_2 := h879c.2.2.1
                                have p879_3 := h879c.2.2.2
                                linarith only [hlam, p879_0]
                        · linarith only [h4, h874, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h4, h868, h873, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h713, h714, h865, h868, h870, hlam, hphi, u5ehi7, u5elo4]
                · linarith only [h712, h865, h868, h869, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h4, h711, h868, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h932 | h932
              · linarith only [h2, h714, h867, h932, hlam, hphi, u5ehi7, u5elo4]
              · linarith only [h4, h711, h932, hc12, hc23, hlam, hphi]
      · linarith only [h4, h711, h713, hlam, hphi, u5ehi7, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h936 | h936
      · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
        · rcases m.htr 1 2 3 (by decide) (by decide) with h938 | h938
          · linarith only [h0, h4, h938, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
            · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
              · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                · linarith only [h0, h4, h712, h941, h942, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · linarith only [h938, h940, h942, hlam]
              · linarith only [h940, h941, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
              · rcases m.htr 1 3 4 (by decide) (by decide) with h947 | h947
                · linarith only [h0, h4, h712, h946, h947, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h949 | h949
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h951 | h951
                      · linarith only [h0, h4, h712, h946, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h0, h4, h946, h951, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h947, h949, h950, hlam, hphi, u5ehi8, u5elo4]
                  · linarith only [h938, h946, h949, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h4, h711, h946, hc12, hc23, hlam, hphi]
        · linarith only [h4, h711, h712, h937, hlam, hphi, u5ehi7, u5elo4]
      · linarith only [h4, h711, h936, hlam, hphi, u5ehi7, u5elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h959 | h959
    · rcases m.htr 0 3 5 (by decide) (by decide) with h960 | h960
      · rcases m.htr 0 4 5 (by decide) (by decide) with h961 | h961
        · rcases m.htr 1 2 3 (by decide) (by decide) with h962 | h962
          · linarith only [h0, h711, h962, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h964 | h964
            · linarith only [h0, h711, h964, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h966 | h966
              · linarith only [h0, h711, h966, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
                · rcases m.htr 1 3 5 (by decide) (by decide) with h969 | h969
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h970 | h970
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h971 | h971
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h972 | h972
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h973 | h973
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h974 | h974
                            · linarith only [h1, h968, h974, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h1bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                rcases p976_3 (m.d 0 1) (by simp) with h978 | h978
                                · rcases p976_3 (m.d 1 2) (by simp) with h979 | h979
                                  · linarith only [h979, hlam, p976_0]
                                  · rcases p976_3 (m.d 1 3) (by simp) with h981 | h981
                                    · linarith only [h1, h981, hlam]
                                    · linarith only [h962, h981, hlam]
                                · linarith only [h978, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h968, h970, h974, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p976_1]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h970, h974, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p976_1]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                rcases p976_3 (m.d 0 1) (by simp) with h987 | h987
                                · rcases p976_3 (m.d 1 2) (by simp) with h988 | h988
                                  · linarith only [h0, h988, hlam]
                                  · rcases p976_3 (m.d 1 3) (by simp) with h990 | h990
                                    · linarith only [h1, h990, hlam]
                                    · linarith only [h969, h990, hlam]
                                · linarith only [h987, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h0, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h962, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h964, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h966, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h1, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                rcases p976_3 (m.d 0 1) (by simp) with h1000 | h1000
                                · rcases p976_3 (m.d 1 2) (by simp) with h1001 | h1001
                                  · linarith only [h1001, h962, hlam]
                                  · rcases p976_3 (m.d 1 3) (by simp) with h1003 | h1003
                                    · rcases p976_3 (m.d 1 4) (by simp) with h1004 | h1004
                                      · linarith only [h1004, h968, hlam]
                                      · linarith only [h1004, h964, hlam]
                                    · linarith only [h1003, h962, hlam]
                                · linarith only [h0, h1000, hlam]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h970, h974, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p976_1]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p976_1, u5ehi6]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h2, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                rcases p976_3 (m.d 0 1) (by simp) with h1013 | h1013
                                · rcases p976_3 (m.d 1 2) (by simp) with h1014 | h1014
                                  · linarith only [h1014, h964, hlam]
                                  · rcases p976_3 (m.d 1 3) (by simp) with h1016 | h1016
                                    · rcases p976_3 (m.d 1 4) (by simp) with h1017 | h1017
                                      · rcases p976_3 (m.d 1 5) (by simp) with h1018 | h1018
                                        · linarith only [h1018, h970, hlam]
                                        · linarith only [h1018, h966, hlam]
                                      · linarith only [h1017, h964, hlam]
                                    · linarith only [h1016, h962, hlam]
                                · linarith only [h0, h1013, hlam]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h968, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h2, h970, h974, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p976_1]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h3, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p976_1, u5elo1]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h969, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [h970, hlam, p976_0]
                              · have p976_0 := h976c.1
                                have p976_1 := h976c.2.1
                                have p976_2 := h976c.2.2.1
                                have p976_3 := h976c.2.2.2
                                linarith only [hlam, p976_0]
                          · linarith only [h964, h970, h973, hlam]
                        · linarith only [h1, h4, h968, h970, h972, hlam, hphi, u5ehi9, u5elo3]
                      · linarith only [h4, h959, h971, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1035 | h1035
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1036 | h1036
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1037 | h1037
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1038 | h1038
                            · linarith only [h1038, h968, h970, hlam]
                            · rcases h1bigk with h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                rcases p1040_3 (m.d 0 1) (by simp) with h1042 | h1042
                                · rcases p1040_3 (m.d 1 2) (by simp) with h1043 | h1043
                                  · linarith only [h1043, hlam, p1040_0]
                                  · rcases p1040_3 (m.d 1 3) (by simp) with h1045 | h1045
                                    · linarith only [h1, h1045, hlam]
                                    · linarith only [h1045, h962, hlam]
                                · linarith only [h1042, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h969, hc01, hlam, hphi, ht0b, ht5b, p1040_1, u5ehi8]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                rcases p1040_3 (m.d 0 1) (by simp) with h1050 | h1050
                                · rcases p1040_3 (m.d 1 2) (by simp) with h1051 | h1051
                                  · linarith only [h0, h1051, hlam]
                                  · rcases p1040_3 (m.d 1 3) (by simp) with h1053 | h1053
                                    · linarith only [h1, h1053, hlam]
                                    · linarith only [h1053, h968, hlam]
                                · linarith only [h1050, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                rcases p1040_3 (m.d 0 1) (by simp) with h1057 | h1057
                                · rcases p1040_3 (m.d 1 2) (by simp) with h1058 | h1058
                                  · linarith only [h0, h1058, hlam]
                                  · rcases p1040_3 (m.d 1 3) (by simp) with h1060 | h1060
                                    · linarith only [h1, h1060, hlam]
                                    · linarith only [h1060, h969, hlam]
                                · linarith only [h1057, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h0, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h962, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h964, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h966, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h1, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                rcases p1040_3 (m.d 0 1) (by simp) with h1070 | h1070
                                · rcases p1040_3 (m.d 1 2) (by simp) with h1071 | h1071
                                  · linarith only [h1071, h962, hlam]
                                  · rcases p1040_3 (m.d 1 3) (by simp) with h1073 | h1073
                                    · rcases p1040_3 (m.d 1 4) (by simp) with h1074 | h1074
                                      · linarith only [h1074, h968, hlam]
                                      · linarith only [h1074, h964, hlam]
                                    · linarith only [h1073, h962, hlam]
                                · linarith only [h0, h1070, hlam]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                rcases p1040_3 (m.d 0 1) (by simp) with h1080 | h1080
                                · rcases p1040_3 (m.d 1 2) (by simp) with h1081 | h1081
                                  · linarith only [h1081, h962, hlam]
                                  · rcases p1040_3 (m.d 1 3) (by simp) with h1083 | h1083
                                    · rcases p1040_3 (m.d 1 4) (by simp) with h1084 | h1084
                                      · linarith only [h1084, h968, hlam]
                                      · rcases p1040_3 (m.d 1 5) (by simp) with h1086 | h1086
                                        · linarith only [h1086, h969, hlam]
                                        · linarith only [h1086, h970, hlam]
                                    · linarith only [h1083, h968, hlam]
                                · linarith only [h1080, h2, hlam]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p1040_1, u5ehi6]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h2, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h1037, h970, hc12, hc24, hlam, hphi, p1040_1]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h968, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h970, hlam, p1040_1]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h3, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1040_1, u5elo1]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h969, hlam, p1040_0]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [h711, h961, h970, hc14, hlam, hphi, ht45, p1040_1, u5elo2]
                              · have p1040_0 := h1040c.1
                                have p1040_1 := h1040c.2.1
                                have p1040_2 := h1040c.2.2.1
                                have p1040_3 := h1040c.2.2.2
                                linarith only [hlam, p1040_0]
                          · linarith only [h1037, h711, h961, h964, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1036, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1035, h4, h959, h961, h964, h970, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h711, h960, h968, h969, hc34, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1106 | h1106
                  · linarith only [h1106, h4, h959, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1108 | h1108
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1111 | h1111
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1112 | h1112
                            · rcases h1bigk with h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c | h1113c
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                rcases p1113_3 (m.d 0 1) (by simp) with h1115 | h1115
                                · rcases p1113_3 (m.d 1 2) (by simp) with h1116 | h1116
                                  · linarith only [h1116, hlam, p1113_0]
                                  · rcases p1113_3 (m.d 1 3) (by simp) with h1118 | h1118
                                    · linarith only [h1, h1118, hlam]
                                    · linarith only [h1118, h962, hlam]
                                · linarith only [h1115, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                rcases p1113_3 (m.d 0 1) (by simp) with h1122 | h1122
                                · rcases p1113_3 (m.d 1 2) (by simp) with h1123 | h1123
                                  · linarith only [h0, h1123, hlam]
                                  · rcases p1113_3 (m.d 1 3) (by simp) with h1125 | h1125
                                    · linarith only [h1125, hlam, p1113_0]
                                    · rcases p1113_3 (m.d 1 4) (by simp) with h1127 | h1127
                                      · linarith only [h1127, h2, hlam]
                                      · linarith only [h1127, h968, hlam]
                                · linarith only [h1122, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h1108, hc01, hlam, hphi, ht0b, ht5b, p1113_1, u5ehi9]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                rcases p1113_3 (m.d 0 1) (by simp) with h1132 | h1132
                                · rcases p1113_3 (m.d 1 2) (by simp) with h1133 | h1133
                                  · linarith only [h0, h1133, hlam]
                                  · rcases p1113_3 (m.d 1 3) (by simp) with h1135 | h1135
                                    · linarith only [h1, h1135, hlam]
                                    · rcases p1113_3 (m.d 1 4) (by simp) with h1137 | h1137
                                      · linarith only [h1137, h2, hlam]
                                      · linarith only [h1108, h1137, hlam]
                                · linarith only [h1132, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h0, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h962, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h964, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h966, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h1, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h1106, h711, h960, hc12, hlam, hphi, ht23, ht34, ht45, p1113_1, u5elo2]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h968, hlam, p1113_1]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h1106, hlam, p1113_1]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h2, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h4, h959, h968, hc12, hc23, hlam, hphi, p1113_1]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h4, h959, h962, h968, hc12, hc23, hlam, hphi, p1113_1]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h4, h959, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1113_1, u5ehi6]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h3, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1113_1, u5elo1]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h1106, h711, h960, h962, hc12, hlam, hphi, ht23, ht34, ht45, p1113_1, u5elo2]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [h1108, hlam, p1113_0]
                              · have p1113_0 := h1113c.1
                                have p1113_1 := h1113c.2.1
                                have p1113_2 := h1113c.2.2.1
                                have p1113_3 := h1113c.2.2.2
                                linarith only [hlam, p1113_0]
                            · linarith only [h1112, h711, h961, h962, h968, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                          · linarith only [h1108, h1109, h1111, h968, hlam]
                        · linarith only [h1110, h4, h711, h959, h960, h968, hc14, hlam, hphi, ht45, u5elo2]
                      · linarith only [h1109, h4, h959, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1165 | h1165
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1166 | h1166
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1167 | h1167
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1168 | h1168
                            · linarith only [h1108, h1168, h4, h959, h962, h968, hc12, hc23, hlam, hphi]
                            · linarith only [h1168, h711, h961, h962, h968, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                          · linarith only [h1167, h711, h961, h964, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h1166, h4, h711, h960, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h1165, h4, h959, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1174 | h1174
          · linarith only [h0, h1174, h4, h711, hc03, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1176 | h1176
            · linarith only [h0, h1176, h711, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
              · linarith only [h1176, h1178, h2, h711, h961, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1181 | h1181
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1182 | h1182
                    · linarith only [h1182, h2, h961, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1184 | h1184
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1185 | h1185
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1186 | h1186
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1187 | h1187
                            · linarith only [h1187, h959, h961, hlam]
                            · rcases h1bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 1) (by simp) with h1191 | h1191
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1192 | h1192
                                  · linarith only [h1192, hlam, p1189_0]
                                  · rcases p1189_3 (m.d 1 3) (by simp) with h1194 | h1194
                                    · linarith only [h1, h1194, hlam]
                                    · linarith only [h1174, h1194, hlam]
                                · linarith only [h1191, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1181, hc01, hlam, hphi, ht0b, ht5b, p1189_1, u5ehi8]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 1) (by simp) with h1199 | h1199
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1200 | h1200
                                  · linarith only [h0, h1200, hlam]
                                  · rcases p1189_3 (m.d 1 3) (by simp) with h1202 | h1202
                                    · linarith only [h1, h1202, hlam]
                                    · linarith only [h1180, h1202, hlam]
                                · linarith only [h1199, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 1) (by simp) with h1206 | h1206
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1207 | h1207
                                  · linarith only [h0, h1207, hlam]
                                  · rcases p1189_3 (m.d 1 3) (by simp) with h1209 | h1209
                                    · linarith only [h1, h1209, hlam]
                                    · linarith only [h1181, h1209, hlam]
                                · linarith only [h1206, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h0, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1174, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1176, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1178, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 1) (by simp) with h1219 | h1219
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1220 | h1220
                                  · linarith only [h1174, h1220, hlam]
                                  · rcases p1189_3 (m.d 1 3) (by simp) with h1222 | h1222
                                    · rcases p1189_3 (m.d 1 4) (by simp) with h1223 | h1223
                                      · linarith only [h1180, h1223, hlam]
                                      · linarith only [h1176, h1223, hlam]
                                    · linarith only [h1174, h1222, hlam]
                                · linarith only [h0, h1219, hlam]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 1) (by simp) with h1229 | h1229
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1230 | h1230
                                  · linarith only [h1174, h1230, hlam]
                                  · rcases p1189_3 (m.d 1 3) (by simp) with h1232 | h1232
                                    · rcases p1189_3 (m.d 1 4) (by simp) with h1233 | h1233
                                      · linarith only [h1180, h1233, hlam]
                                      · rcases p1189_3 (m.d 1 5) (by simp) with h1235 | h1235
                                        · linarith only [h1181, h1235, hlam]
                                        · linarith only [h1182, h1235, hlam]
                                    · linarith only [h1180, h1232, hlam]
                                · linarith only [h1229, h2, hlam]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1, h1181, hc01, hlam, hphi, ht0b, ht5b, p1189_1, u5ehi8]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h2, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1186, h2, h961, hc12, hlam, hphi, ht23, ht34, ht45, p1189_1, u5elo2]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1180, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1182, hlam, p1189_1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h3, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht23, ht34, ht45, p1189_1, u5elo0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1181, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1186, h3, h961, hc14, hlam, hphi, ht45, p1189_1, u5elo2]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                          · linarith only [h1176, h1186, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1185, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1184, h4, h959, hlam]
                  · linarith only [h1180, h1181, h711, h960, hc34, hlam, hphi, ht45, u5elo2]
                · linarith only [h1174, h1180, h959, h961, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
      · linarith only [h959, h960, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1257 | h1257
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1258 | h1258
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1259 | h1259
          · linarith only [h0, h1259, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1261 | h1261
            · linarith only [h0, h1261, h711, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1263 | h1263
              · linarith only [h0, h1263, h711, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1265 | h1265
                · linarith only [h1257, h1265, h959, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1267 | h1267
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1268 | h1268
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1269 | h1269
                      · linarith only [h1, h1267, h1269, h959, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1271 | h1271
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1272 | h1272
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1273 | h1273
                            · rcases h1bigk with h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                rcases p1274_3 (m.d 0 1) (by simp) with h1276 | h1276
                                · rcases p1274_3 (m.d 1 2) (by simp) with h1277 | h1277
                                  · linarith only [h1277, hlam, p1274_0]
                                  · rcases p1274_3 (m.d 1 3) (by simp) with h1279 | h1279
                                    · linarith only [h1, h1279, hlam]
                                    · linarith only [h1259, h1279, hlam]
                                · linarith only [h1276, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1267, h1273, hc01, hlam, hphi, ht0b, ht5b, p1274_1, u5ehi9]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1265, h1267, h1273, hc01, hlam, hphi, ht0b, ht5b, p1274_1, u5ehi9]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                rcases p1274_3 (m.d 0 1) (by simp) with h1285 | h1285
                                · rcases p1274_3 (m.d 1 2) (by simp) with h1286 | h1286
                                  · linarith only [h0, h1286, hlam]
                                  · rcases p1274_3 (m.d 1 3) (by simp) with h1288 | h1288
                                    · linarith only [h1, h1288, hlam]
                                    · linarith only [h1267, h1288, hlam]
                                · linarith only [h1285, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h0, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1259, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1261, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1263, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1, h1269, h4, hc12, hc34, hlam, hphi, ht23, p1274_1]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1265, hlam, p1274_1]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1, h1269, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1274_1, u5ehi6]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h2, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                rcases p1274_3 (m.d 0 1) (by simp) with h1303 | h1303
                                · rcases p1274_3 (m.d 1 2) (by simp) with h1304 | h1304
                                  · linarith only [h1261, h1304, hlam]
                                  · rcases p1274_3 (m.d 1 3) (by simp) with h1306 | h1306
                                    · linarith only [h1265, h1306, hlam]
                                    · linarith only [h1259, h1306, hlam]
                                · linarith only [h0, h1303, hlam]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1261, h1267, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1274_1, u5ehi8]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1267, h1273, h2, hc01, hlam, hphi, ht0b, ht5b, p1274_1, u5ehi9]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h3, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1, h1267, h1269, h1273, h4, hc12, hc34, hlam, hphi, ht23, p1274_1, u5ehi9, u5elo1]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1267, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [h1268, hlam, p1274_0]
                              · have p1274_0 := h1274c.1
                                have p1274_1 := h1274c.2.1
                                have p1274_2 := h1274c.2.2.1
                                have p1274_3 := h1274c.2.2.2
                                linarith only [hlam, p1274_0]
                            · linarith only [h1, h1267, h1269, h1273, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h1261, h1268, h1272, h3, h711, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h1, h1267, h1271, h4, hlam]
                    · linarith only [h1258, h1265, h1267, h1268, h711, hlam, hphi, u5ehi8, u5elo2]
                  · linarith only [h1257, h1267, h959, hc13, hc34, hlam, hphi]
        · linarith only [h1257, h1258, h959, hlam, hphi, u5ehi8, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1324 | h1324
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1325 | h1325
          · linarith only [h0, h1325, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1327 | h1327
            · linarith only [h0, h1257, h1327, h4, hc24, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1329 | h1329
              · linarith only [h0, h1257, h1329, h4, h711, hlam, hphi, u5ehi5, u5elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1331 | h1331
                · linarith only [h1, h1257, h1331, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1333 | h1333
                  · linarith only [h1, h1257, h1333, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1335 | h1335
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1336 | h1336
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1337 | h1337
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1338 | h1338
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1339 | h1339
                            · rcases h1bigk with h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                rcases p1340_3 (m.d 0 1) (by simp) with h1342 | h1342
                                · rcases p1340_3 (m.d 1 2) (by simp) with h1343 | h1343
                                  · linarith only [h1343, hlam, p1340_0]
                                  · rcases p1340_3 (m.d 1 3) (by simp) with h1345 | h1345
                                    · linarith only [h1, h1345, hlam]
                                    · linarith only [h1325, h1345, hlam]
                                · linarith only [h1342, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                rcases p1340_3 (m.d 0 1) (by simp) with h1349 | h1349
                                · rcases p1340_3 (m.d 1 2) (by simp) with h1350 | h1350
                                  · linarith only [h0, h1350, hlam]
                                  · rcases p1340_3 (m.d 1 3) (by simp) with h1352 | h1352
                                    · linarith only [h1352, hlam, p1340_0]
                                    · rcases p1340_3 (m.d 1 4) (by simp) with h1354 | h1354
                                      · linarith only [h1354, h2, hlam]
                                      · linarith only [h1331, h1354, hlam]
                                · linarith only [h1349, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1335, hc01, hlam, hphi, ht0b, ht5b, p1340_1, u5ehi9]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                rcases p1340_3 (m.d 0 1) (by simp) with h1359 | h1359
                                · rcases p1340_3 (m.d 1 2) (by simp) with h1360 | h1360
                                  · linarith only [h0, h1360, hlam]
                                  · rcases p1340_3 (m.d 1 3) (by simp) with h1362 | h1362
                                    · linarith only [h1, h1362, hlam]
                                    · rcases p1340_3 (m.d 1 4) (by simp) with h1364 | h1364
                                      · linarith only [h1364, h2, hlam]
                                      · linarith only [h1335, h1364, hlam]
                                · linarith only [h1359, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h0, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1325, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1327, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1329, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1, h1257, h1337, hc12, hlam, hphi, ht23, ht34, ht45, p1340_1, u5elo2]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1331, hlam, p1340_1]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1333, hlam, p1340_1]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h2, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1336, h2, h959, hc12, hc23, hlam, hphi, p1340_1]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1325, h1336, h2, h959, hc12, hc23, hlam, hphi, p1340_1]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1335, h1336, h2, h959, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1340_1, u5ehi9]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h3, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht23, ht34, ht45, p1340_1, u5elo0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1325, h3, h711, hc12, hlam, hphi, ht23, ht34, ht45, p1340_1, u5elo2]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [h1335, hlam, p1340_0]
                              · have p1340_0 := h1340c.1
                                have p1340_1 := h1340c.2.1
                                have p1340_2 := h1340c.2.2.1
                                have p1340_3 := h1340c.2.2.2
                                linarith only [hlam, p1340_0]
                            · linarith only [h0, h1339, h4, h959, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1335, h1336, h1338, h2, h959, hlam]
                        · linarith only [h0, h1337, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1391 | h1391
                        · linarith only [h0, h1257, h1336, h1391, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1391, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1394 | h1394
                      · linarith only [h1324, h1325, h1331, h1335, h1394, h959, hc12, hc23, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1396 | h1396
                        · linarith only [h0, h1257, h1394, h1396, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1396, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1399 | h1399
          · linarith only [h0, h1399, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1401 | h1401
            · linarith only [h0, h1401, h711, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1403 | h1403
              · linarith only [h0, h1324, h1403, h4, h959, hlam, hphi, u5ehi7, u5elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1405 | h1405
                · linarith only [h1, h1324, h1405, h959, hc34, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1407 | h1407
                  · linarith only [h1, h1324, h1407, h959, hlam, hphi, u5ehi8, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1409 | h1409
                    · linarith only [h1324, h1409, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1411 | h1411
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1412 | h1412
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1413 | h1413
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1414 | h1414
                            · linarith only [h0, h1324, h1411, h1414, h4, h959, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1413, h1414, h4, h959, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                          · linarith only [h1401, h1413, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1412, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1419 | h1419
                        · linarith only [h0, h1257, h1411, h1419, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1419, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1423 | h1423
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1424 | h1424
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1425 | h1425
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1426 | h1426
        · linarith only [h1, h1426, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1428 | h1428
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1429 | h1429
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1430 | h1430
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1431 | h1431
                · linarith only [h0, h1431, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1433 | h1433
                  · linarith only [h0, h1431, h1433, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                  · linarith only [h0, h1425, h1431, h1433, h2, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1436 | h1436
                · linarith only [h0, h1424, h1430, h1436, h2, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1424, h1430, h1436, h2, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1424, h1429, h2, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1440 | h1440
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1442 | h1442
                · linarith only [h0, h1442, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1444 | h1444
                  · linarith only [h0, h1444, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h0, h1425, h1442, h1444, h2, hc12, hc24, hlam, hphi]
              · linarith only [h1424, h1428, h1441, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h1440, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
      · linarith only [h1424, h1425, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1450 | h1450
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1451 | h1451
        · linarith only [h1, h1451, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1453 | h1453
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1454 | h1454
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1455 | h1455
              · linarith only [h1424, h1450, h1455, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
                · linarith only [h1, h1455, h1457, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
                  · linarith only [h1, h1455, h1459, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h1424, h1450, h1459, hc12, hc23, hlam, hphi]
            · linarith only [h1, h1424, h1450, h1454, h2, hlam, hphi, u5ehi7, u5elo4]
          · linarith only [h1424, h1450, h1453, hlam, hphi, u5ehi7, u5elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1464 | h1464
        · linarith only [h1, h1464, h2, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1466 | h1466
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1467 | h1467
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1468 | h1468
              · linarith only [h0, h1424, h1450, h1468, hc03, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1470 | h1470
                · linarith only [h0, h1450, h1470, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1472 | h1472
                  · linarith only [h0, h1450, h1472, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1474 | h1474
                    · linarith only [h1464, h1466, h1474, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1476 | h1476
                      · linarith only [h1, h1474, h1476, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · linarith only [h1, h1466, h1474, h1476, h2, hc13, hc34, hlam, hphi]
            · linarith only [h0, h1467, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1480 | h1480
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1481 | h1481
              · linarith only [h0, h1424, h1481, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1483 | h1483
                · linarith only [h1, h1466, h1481, h1483, hc24, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
                  · linarith only [h1, h1466, h1481, h1485, hlam, hphi, u5ehi7, u5elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
                    · linarith only [h1, h1464, h1466, h1487, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1489 | h1489
                      · linarith only [h1, h1466, h1489, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1491 | h1491
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1492 | h1492
                          · linarith only [h1423, h1487, h1491, h1492, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1494 | h1494
                            · linarith only [h1424, h1466, h1492, h1494, hc02, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1424, h1494, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h1423, h1491, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
            · linarith only [h1423, h1480, h2, hlam, hphi, u5ehi6, u5elo4]
  · linarith only [h0, h1423, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2

end R2N4
