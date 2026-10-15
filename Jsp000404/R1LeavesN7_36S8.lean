import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h778 | h778
  · rcases m.htr 0 3 4 (by decide) (by decide) with h779 | h779
    · rcases m.htr 0 3 5 (by decide) (by decide) with h780 | h780
      · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
        · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
          · linarith only [h0, h3, h778, h782, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
            · rcases m.htr 1 3 4 (by decide) (by decide) with h785 | h785
              · rcases m.htr 1 3 5 (by decide) (by decide) with h786 | h786
                · rcases m.htr 1 4 5 (by decide) (by decide) with h787 | h787
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h790 | h790
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h791 | h791
                          · rcases h3bigk with h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h782, h784, h788, h791, hc03, hc45, hlam, hphi, ht0b, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h3, hlam, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              rcases p792_3 (m.d 0 3) (by simp) with h796 | h796
                              · rcases p792_3 (m.d 1 3) (by simp) with h797 | h797
                                · linarith only [h1, h797, hlam]
                                · linarith only [h785, h797, hlam]
                              · linarith only [h796, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              rcases p792_3 (m.d 0 3) (by simp) with h801 | h801
                              · rcases p792_3 (m.d 1 3) (by simp) with h802 | h802
                                · linarith only [h1, h802, hlam]
                                · linarith only [h786, h802, hlam]
                              · linarith only [h801, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h1, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h782, hlam, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h1, h791, hc01, hc45, hlam, hphi, ht0b, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              rcases p792_3 (m.d 0 3) (by simp) with h810 | h810
                              · rcases p792_3 (m.d 1 3) (by simp) with h811 | h811
                                · rcases p792_3 (m.d 2 3) (by simp) with h812 | h812
                                  · rcases p792_3 (m.d 3 4) (by simp) with h813 | h813
                                    · linarith only [h785, h813, hlam]
                                    · linarith only [h791, h813, hlam]
                                  · linarith only [h789, h812, hlam]
                                · linarith only [h811, hlam, p792_0]
                              · linarith only [h780, h810, hlam]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h0, h3, h784, h788, h791, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h782, h784, h788, h791, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              rcases p792_3 (m.d 0 3) (by simp) with h822 | h822
                              · linarith only [h3, h822, hlam]
                              · linarith only [h779, h822, hlam]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              rcases p792_3 (m.d 0 3) (by simp) with h825 | h825
                              · linarith only [h3, h825, hlam]
                              · linarith only [h780, h825, hlam]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h779, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h785, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h788, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h0, h3, h784, h788, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h780, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h786, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h789, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h791, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                          · linarith only [h781, h791, hc34, hlam, hphi, u4elo0]
                        · linarith only [h787, h790, hc24, hlam, hphi, u4elo1]
                      · linarith only [h3, h778, h780, h788, h789, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3, h788, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h781, h787, hc14, hlam, hphi, u4elo0]
                · linarith only [h780, h781, h782, h784, h786, hc24, hlam, hphi, u4elo0]
              · linarith only [h782, h784, h785, hc24, hlam, hphi, u4elo3]
            · linarith only [h3, h778, h784, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h846 | h846
          · linarith only [h0, h3, h846, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
            · rcases m.htr 1 3 4 (by decide) (by decide) with h849 | h849
              · rcases m.htr 1 3 5 (by decide) (by decide) with h850 | h850
                · rcases m.htr 1 4 5 (by decide) (by decide) with h851 | h851
                  · linarith only [h781, h851, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h855 | h855
                        · linarith only [h2, h781, h848, h855, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h857 | h857
                          · linarith only [h2, h781, h848, h853, h857, hlam]
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
                              rcases p859_3 (m.d 0 3) (by simp) with h861 | h861
                              · rcases p859_3 (m.d 1 3) (by simp) with h862 | h862
                                · linarith only [h1, h862, hlam]
                                · rcases p859_3 (m.d 2 3) (by simp) with h864 | h864
                                  · rcases p859_3 (m.d 3 4) (by simp) with h865 | h865
                                    · linarith only [h779, h865, hlam]
                                    · rcases p859_3 (m.d 3 5) (by simp) with h867 | h867
                                      · linarith only [h780, h867, hlam]
                                      · rcases h3emin with h869 | h869 | h869 | h869 | h869
                                        · rcases h4bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h781, h848, h853, hc34, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h781, h853, hc34, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h781, hc34, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h781, hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h2, hlam, p870_1]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p870_1, u4elo1]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h2, h781, hc34, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h851, hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h778, hlam, p870_1]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h848, hlam, p870_1]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hc34, hlam, hphi, p870_1, u4elo2]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h855, hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h779, hlam, p870_1]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h849, hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h853, hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h857, hlam, p870_0]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hc04, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h848, hc24, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hc34, hlam, hphi, p870_1, u4elo4]
                                          · have p870_0 := h870c.1
                                            have p870_1 := h870c.2.1
                                            have p870_2 := h870c.2.2.1
                                            have p870_3 := h870c.2.2.2
                                            linarith only [hlam, p870_0]
                                        · linarith only [h3, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1]
                                        · rcases h4bigk with h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h848, h853, hc34, hlam, hphi, p897_1, u4elo0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p897_1, u4elo0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hc34, hlam, hphi, p897_1, u4elo0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h781, hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h2, hlam, p897_1]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p897_1, u4elo1]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h2, h781, hc34, hlam, hphi, p897_1, u4elo4]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h851, hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h778, hlam, p897_1]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h848, hlam, p897_1]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hc34, hlam, hphi, p897_1, u4elo2]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h855, hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h779, hlam, p897_1]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h849, hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h853, hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h857, hlam, p897_0]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hc04, hlam, hphi, p897_1, u4elo4]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h848, hc24, hlam, hphi, p897_1, u4elo4]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p897_1, u4elo4]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hc34, hlam, hphi, p897_1, u4elo4]
                                          · have p897_0 := h897c.1
                                            have p897_1 := h897c.2.1
                                            have p897_2 := h897c.2.2.1
                                            have p897_3 := h897c.2.2.2
                                            linarith only [hlam, p897_0]
                                        · linarith only [h2, h848, h853, h869, hlam, ht34, u4elo0]
                                        · linarith only [h3, h850, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1]
                                  · linarith only [h846, h864, hlam]
                              · linarith only [h1, h861, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h3, hlam, p859_1]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h928 | h928
                              · rcases p859_3 (m.d 1 3) (by simp) with h929 | h929
                                · linarith only [h1, h929, hlam]
                                · linarith only [h849, h929, hlam]
                              · linarith only [h928, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h933 | h933
                              · rcases p859_3 (m.d 1 3) (by simp) with h934 | h934
                                · linarith only [h1, h934, hlam]
                                · linarith only [h850, h934, hlam]
                              · linarith only [h933, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h1, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h846, hlam, p859_1]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h941 | h941
                              · rcases p859_3 (m.d 1 3) (by simp) with h942 | h942
                                · rcases p859_3 (m.d 2 3) (by simp) with h943 | h943
                                  · rcases p859_3 (m.d 3 4) (by simp) with h944 | h944
                                    · linarith only [h944, hlam, p859_0]
                                    · rcases p859_3 (m.d 3 5) (by simp) with h946 | h946
                                      · linarith only [h850, h946, hlam]
                                      · linarith only [h857, h946, hlam]
                                  · linarith only [h853, h943, hlam]
                                · linarith only [h942, hlam, p859_0]
                              · linarith only [h779, h941, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h952 | h952
                              · rcases p859_3 (m.d 1 3) (by simp) with h953 | h953
                                · rcases p859_3 (m.d 2 3) (by simp) with h954 | h954
                                  · rcases p859_3 (m.d 3 4) (by simp) with h955 | h955
                                    · linarith only [h849, h955, hlam]
                                    · rcases p859_3 (m.d 3 5) (by simp) with h957 | h957
                                      · linarith only [h957, hlam, p859_0]
                                      · rcases h3emin with h959 | h959 | h959 | h959 | h959
                                        · rcases h4bigk with h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h781, hc14, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h781, hc24, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h781, hc34, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h781, hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h2, hlam, p960_1]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p960_1, u4elo1]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h2, h781, hc34, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h851, hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h778, hlam, p960_1]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h848, hlam, p960_1]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hc34, hlam, hphi, p960_1, u4elo2]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h855, hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h779, hlam, p960_1]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h849, hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h853, hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h857, hlam, p960_0]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hc04, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h848, hc24, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hc34, hlam, hphi, p960_1, u4elo4]
                                          · have p960_0 := h960c.1
                                            have p960_1 := h960c.2.1
                                            have p960_2 := h960c.2.2.1
                                            have p960_3 := h960c.2.2.2
                                            linarith only [hlam, p960_0]
                                        · rcases h4bigk with h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h781, h848, h853, hc34, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h781, h853, hc34, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h781, hc34, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h781, hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h2, hlam, p986_1]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p986_1, u4elo1]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h2, h781, hc34, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h851, hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h778, hlam, p986_1]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h848, hlam, p986_1]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hc34, hlam, hphi, p986_1, u4elo2]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h855, hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h779, hlam, p986_1]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h849, hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h853, hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h857, hlam, p986_0]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hc04, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h848, hc24, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hc34, hlam, hphi, p986_1, u4elo4]
                                          · have p986_0 := h986c.1
                                            have p986_1 := h986c.2.1
                                            have p986_2 := h986c.2.2.1
                                            have p986_3 := h986c.2.2.2
                                            linarith only [hlam, p986_0]
                                        · rcases h4bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h781, h848, h853, hc34, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h781, h853, hc34, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h781, hc34, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h781, hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h2, hlam, p1012_1]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p1012_1, u4elo1]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h2, h781, hc34, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h851, hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h778, hlam, p1012_1]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h848, hlam, p1012_1]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hc34, hlam, hphi, p1012_1, u4elo2]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h855, hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h779, hlam, p1012_1]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h849, hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h853, hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h857, hlam, p1012_0]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hc04, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h848, hc24, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hc34, hlam, hphi, p1012_1, u4elo4]
                                          · have p1012_0 := h1012c.1
                                            have p1012_1 := h1012c.2.1
                                            have p1012_2 := h1012c.2.2.1
                                            have p1012_3 := h1012c.2.2.2
                                            linarith only [hlam, p1012_0]
                                        · linarith only [h857, h959, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1]
                                        · linarith only [h959, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1]
                                  · linarith only [h854, h954, hlam]
                                · linarith only [h953, hlam, p859_0]
                              · linarith only [h780, h952, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h1043 | h1043
                              · linarith only [h1043, h3, hlam]
                              · rcases p859_3 (m.d 1 3) (by simp) with h1045 | h1045
                                · linarith only [h1045, h846, hlam]
                                · rcases p859_3 (m.d 2 3) (by simp) with h1047 | h1047
                                  · rcases p859_3 (m.d 3 4) (by simp) with h1048 | h1048
                                    · linarith only [h1048, h853, hlam]
                                    · rcases p859_3 (m.d 3 5) (by simp) with h1050 | h1050
                                      · linarith only [h1050, h854, hlam]
                                      · rcases h3emin with h1052 | h1052 | h1052 | h1052 | h1052
                                        · linarith only [h1052, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1]
                                        · linarith only [h1, h1052, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1]
                                        · rcases h4bigk with h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h848, h853, hc34, hlam, hphi, p1055_1, u4elo0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h3, h778, h853, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1055_1, p859_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h3, h778, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1055_1, p859_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h781, hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h2, hlam, p1055_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p1055_1, u4elo1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h2, h781, hc34, hlam, hphi, p1055_1, u4elo4]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h851, hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h778, hlam, p1055_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h848, hlam, p1055_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h1, h846, h848, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1055_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h855, hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h779, hlam, p1055_1]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h849, hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h853, hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h857, hlam, p1055_0]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hc04, hlam, hphi, p1055_1, u4elo4]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hc14, hlam, hphi, p1055_1, u4elo4]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [h853, hc34, hlam, hphi, p1055_1, u4elo4]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hc34, hlam, hphi, p1055_1, u4elo4]
                                          · have p1055_0 := h1055c.1
                                            have p1055_1 := h1055c.2.1
                                            have p1055_2 := h1055c.2.2.1
                                            have p1055_3 := h1055c.2.2.2
                                            linarith only [hlam, p1055_0]
                                        · linarith only [h1052, h2, h848, h853, hlam, ht34, u4elo0]
                                        · linarith only [h1052, h780, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1]
                                  · linarith only [h1047, h3, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h1084 | h1084
                              · linarith only [h1084, h3, hlam]
                              · linarith only [h1, h1084, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h1088 | h1088
                              · linarith only [h1088, h3, hlam]
                              · linarith only [h1088, h779, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              rcases p859_3 (m.d 0 3) (by simp) with h1091 | h1091
                              · linarith only [h1091, h3, hlam]
                              · linarith only [h1091, h780, hlam]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h779, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h849, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h853, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h857, hlam, p859_1]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h780, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h850, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h854, hlam, p859_0]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [h1, h850, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p859_1]
                            · have p859_0 := h859c.1
                              have p859_1 := h859c.2.1
                              have p859_2 := h859c.2.2.1
                              have p859_3 := h859c.2.2.2
                              linarith only [hlam, p859_0]
                      · linarith only [h0, h1, h3, h848, h850, h853, h854, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3, h853, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h780, h781, h846, h848, h850, hc24, hlam, hphi, u4elo4]
              · linarith only [h846, h848, h849, hc24, hlam, hphi, u4elo3]
            · linarith only [h3, h778, h848, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1109 | h1109
        · linarith only [h1109, h3, h778, h780, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
          · linarith only [h0, h1111, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1113 | h1113
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                · linarith only [h0, h1, h1113, h1115, h3, h780, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1117 | h1117
                  · linarith only [h1109, h1117, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1119 | h1119
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1120 | h1120
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1121 | h1121
                        · linarith only [h0, h1109, h1113, h1120, h1121, h3, h780, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1113, h1120, h1121, h3, h780, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1124 | h1124
                        · linarith only [h0, h1113, h1117, h1120, h1124, h3, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1113, h1119, h1120, h1124, h3, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h1113, h1119, h3, hc24, hlam, hphi, u4elo3]
              · linarith only [h1114, h779, h780, hc13, hc35, hlam, hphi]
            · linarith only [h1113, h3, h778, hc12, hc23, hlam, hphi]
    · linarith only [h3, h778, h779, hc24, hlam, hphi, u4elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1131 | h1131
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1132 | h1132
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1134 | h1134
          · linarith only [h0, h1134, h778, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1136 | h1136
            · linarith only [h0, h1136, h778, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1138 | h1138
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1139 | h1139
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1140 | h1140
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1141 | h1141
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1142 | h1142
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1143 | h1143
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1144 | h1144
                          · rcases h3bigk with h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1138, h1144, hc03, hc45, hlam, hphi, ht0b, ht5b, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h3, hlam, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              rcases p1145_3 (m.d 0 3) (by simp) with h1149 | h1149
                              · rcases p1145_3 (m.d 1 3) (by simp) with h1150 | h1150
                                · linarith only [h1, h1150, hlam]
                                · linarith only [h1138, h1150, hlam]
                              · linarith only [h1149, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              rcases p1145_3 (m.d 0 3) (by simp) with h1154 | h1154
                              · rcases p1145_3 (m.d 1 3) (by simp) with h1155 | h1155
                                · linarith only [h1, h1155, hlam]
                                · linarith only [h1139, h1155, hlam]
                              · linarith only [h1154, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1134, hlam, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1, h1144, hc01, hc45, hlam, hphi, ht0b, ht5b, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              rcases p1145_3 (m.d 0 3) (by simp) with h1163 | h1163
                              · rcases p1145_3 (m.d 1 3) (by simp) with h1164 | h1164
                                · rcases p1145_3 (m.d 2 3) (by simp) with h1165 | h1165
                                  · rcases p1145_3 (m.d 3 4) (by simp) with h1166 | h1166
                                    · linarith only [h1138, h1166, hlam]
                                    · linarith only [h1144, h1166, hlam]
                                  · linarith only [h1142, h1165, hlam]
                                · linarith only [h1164, hlam, p1145_0]
                              · linarith only [h1132, h1163, hlam]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1131, h1144, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1138, h1144, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              rcases p1145_3 (m.d 0 3) (by simp) with h1175 | h1175
                              · linarith only [h1175, h3, hlam]
                              · linarith only [h1131, h1175, hlam]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              rcases p1145_3 (m.d 0 3) (by simp) with h1178 | h1178
                              · linarith only [h1178, h3, hlam]
                              · linarith only [h1132, h1178, hlam]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1131, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1138, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1141, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1, h1138, hc01, hc35, hlam, hphi, ht0b, ht5b, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1132, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1139, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1142, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1144, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                          · linarith only [h1133, h1144, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1143, h778, hc02, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h1132, h1142, h3, hlam]
                    · linarith only [h0, h1141, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1133, h1140, hc14, hlam, hphi, u4elo0]
                · linarith only [h1132, h1133, h1138, h1139, h778, hc34, hlam, hphi, u4elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1197 | h1197
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1200 | h1200
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1201 | h1201
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1202 | h1202
                          · rcases h3bigk with h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              rcases p1203_3 (m.d 0 3) (by simp) with h1205 | h1205
                              · rcases p1203_3 (m.d 1 3) (by simp) with h1206 | h1206
                                · linarith only [h1, h1206, hlam]
                                · rcases p1203_3 (m.d 2 3) (by simp) with h1208 | h1208
                                  · rcases p1203_3 (m.d 3 4) (by simp) with h1209 | h1209
                                    · linarith only [h1131, h1209, hlam]
                                    · linarith only [h1138, h1209, hlam]
                                  · linarith only [h1134, h1208, hlam]
                              · linarith only [h1, h1205, hlam]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h3, hlam, p1203_1]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1138, h1197, h1202, hc03, hc45, hlam, hphi, ht0b, ht5b, p1203_1]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1131, h1138, h1197, hlam, p1203_2]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1134, hlam, p1203_1]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1138, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1131, h1138, h1202, h778, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1203_1, u4elo2]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1131, h1134, h1138, hc12, hc23, hlam, hphi, p1203_1]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              rcases p1203_3 (m.d 0 3) (by simp) with h1223 | h1223
                              · linarith only [h1223, h3, hlam]
                              · linarith only [h1, h1223, hlam]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1138, h1197, h1202, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1203_1]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1131, h1138, h1197, h3, hlam, p1203_2]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1131, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1131, h1197, h1202, hc03, hc45, hlam, hphi, ht0b, ht5b, p1203_1]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1199, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              rcases p1203_3 (m.d 0 3) (by simp) with h1233 | h1233
                              · rcases p1203_3 (m.d 1 3) (by simp) with h1234 | h1234
                                · linarith only [h1138, h1234, hlam]
                                · linarith only [h1197, h1234, hlam]
                              · linarith only [h1132, h1233, hlam]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1132, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1197, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1200, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [h1202, hlam, p1203_0]
                            · have p1203_0 := h1203c.1
                              have p1203_1 := h1203c.2.1
                              have p1203_2 := h1203c.2.2.1
                              have p1203_3 := h1203c.2.2.2
                              linarith only [hlam, p1203_0]
                          · linarith only [h1133, h1202, h778, hc34, hlam, hphi, u4elo2]
                        · linarith only [h1131, h1138, h1197, h1198, h1201, h778, hlam]
                      · linarith only [h1131, h1138, h1197, h1200, h3, h778, hc03, hlam, hphi, ht34, u4elo2]
                    · linarith only [h1131, h1199, h3, hlam]
                  · linarith only [h1133, h1198, h778, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1248 | h1248
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1249 | h1249
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1250 | h1250
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1252 | h1252
                          · rcases h3bigk with h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              rcases p1253_3 (m.d 0 3) (by simp) with h1255 | h1255
                              · rcases p1253_3 (m.d 1 3) (by simp) with h1256 | h1256
                                · linarith only [h1, h1256, hlam]
                                · rcases p1253_3 (m.d 2 3) (by simp) with h1258 | h1258
                                  · rcases p1253_3 (m.d 3 4) (by simp) with h1259 | h1259
                                    · linarith only [h1131, h1259, hlam]
                                    · linarith only [h1138, h1259, hlam]
                                  · linarith only [h1134, h1258, hlam]
                              · linarith only [h1, h1255, hlam]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h3, hlam, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1134, h1138, h3, hc12, hc23, hlam, hphi, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1134, h1197, h3, hc12, hc23, hlam, hphi, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1134, hlam, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1138, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1197, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1131, h1132, h1133, h1134, h1197, hc12, hc23, hlam, hphi, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              rcases p1253_3 (m.d 0 3) (by simp) with h1273 | h1273
                              · linarith only [h1273, h3, hlam]
                              · linarith only [h1, h1273, hlam]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1134, h1197, h1252, hc12, hc23, hlam, hphi, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1134, h1197, hc12, hc23, hlam, hphi, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1131, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1134, hc12, hlam, hphi, ht23, ht34, p1253_1, u4elo3]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1249, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1131, h1134, h1197, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1132, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1132, h1134, h3, hc12, hc23, hlam, hphi, p1253_1]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1250, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [h1252, hlam, p1253_0]
                            · have p1253_0 := h1253c.1
                              have p1253_1 := h1253c.2.1
                              have p1253_2 := h1253c.2.2.1
                              have p1253_3 := h1253c.2.2.2
                              linarith only [hlam, p1253_0]
                          · linarith only [h1248, h1252, hc34, hlam, hphi, u4elo1]
                        · linarith only [h1131, h1138, h1248, h1251, h778, hlam]
                      · linarith only [h0, h1132, h1133, h1250, h3, h778, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h1131, h1249, h3, hlam]
                  · linarith only [h1133, h1248, h778, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1294 | h1294
          · linarith only [h0, h1294, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1296 | h1296
            · linarith only [h0, h1133, h1296, h778, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1298 | h1298
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1299 | h1299
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1300 | h1300
                  · linarith only [h1133, h1300, h778, hc02, hlam, hphi, ht23, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1302 | h1302
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1303 | h1303
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1304 | h1304
                        · linarith only [h0, h1133, h1304, h778, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1304, h778, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h1, h1299, h1303, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1302, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h1132, h1133, h1298, h1299, hc34, hlam, hphi, u4elo4]
              · linarith only [h1131, h1133, h1298, hc13, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1311 | h1311
        · linarith only [h1131, h1132, h1311, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1313 | h1313
          · linarith only [h0, h1313, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1315 | h1315
            · linarith only [h0, h1311, h1315, h778, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1317 | h1317
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1318 | h1318
                · linarith only [h1, h1132, h1318, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h1311, h1320, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1322 | h1322
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1323 | h1323
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1324 | h1324
                        · linarith only [h1311, h1324, h778, hc02, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1324, h778, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1327 | h1327
                        · linarith only [h0, h1311, h1327, h778, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1327, h778, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h1322, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h1131, h1132, h1311, h1317, hc13, hlam, hphi, ht34, u4elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1332 | h1332
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1333 | h1333
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1334 | h1334
          · linarith only [h0, h1334, h778, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1336 | h1336
            · linarith only [h0, h1131, h1336, h3, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
              · linarith only [h1, h1131, h1332, h1338, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1340 | h1340
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1341 | h1341
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1342 | h1342
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1343 | h1343
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1344 | h1344
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1345 | h1345
                          · rcases h3bigk with h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1131, h1342, hc13, hlam, hphi, ht34, p1346_1, u4elo2]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h3, hlam, p1346_1]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1131, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1131, h1342, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1346_1, u4elo2]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1334, hlam, p1346_1]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1338, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1, h1131, h1342, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1346_1, u4elo2]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              rcases p1346_3 (m.d 0 3) (by simp) with h1357 | h1357
                              · linarith only [h1357, h3, hlam]
                              · rcases p1346_3 (m.d 1 3) (by simp) with h1359 | h1359
                                · linarith only [h1334, h1359, hlam]
                                · rcases p1346_3 (m.d 2 3) (by simp) with h1361 | h1361
                                  · rcases p1346_3 (m.d 3 4) (by simp) with h1362 | h1362
                                    · linarith only [h1342, h1362, hlam]
                                    · linarith only [h1131, h1362, hlam]
                                  · linarith only [h1361, h3, hlam]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              rcases p1346_3 (m.d 0 3) (by simp) with h1366 | h1366
                              · linarith only [h1366, h3, hlam]
                              · linarith only [h1, h1366, hlam]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h0, h1131, h3, hc12, hc23, hlam, hphi, p1346_1]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1, h1131, h1340, h1342, hlam, p1346_2]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1, h1340, h1342, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1346_1, u4elo2]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1340, h1342, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1346_1, u4elo2]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1342, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              rcases p1346_3 (m.d 0 3) (by simp) with h1376 | h1376
                              · linarith only [h1131, h1376, hlam]
                              · linarith only [h1332, h1376, hlam]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1332, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1340, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1343, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [h1345, hlam, p1346_0]
                            · have p1346_0 := h1346c.1
                              have p1346_1 := h1346c.2.1
                              have p1346_2 := h1346c.2.2.1
                              have p1346_3 := h1346c.2.2.2
                              linarith only [hlam, p1346_0]
                          · linarith only [h1131, h1345, h3, hc02, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h1341, h1344, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1, h1131, h1340, h1342, h1343, hlam]
                    · linarith only [h0, h1342, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1131, h1332, h1333, h1341, hc14, hlam, hphi, u4elo3]
                · linarith only [h1131, h1332, h1340, hc13, hlam, hphi, ht34, u4elo3]
        · linarith only [h1131, h1332, h1333, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1391 | h1391
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1392 | h1392
          · linarith only [h0, h1392, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1394 | h1394
            · linarith only [h0, h1394, h778, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
              · linarith only [h1, h1131, h1396, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1398 | h1398
                · linarith only [h1, h1332, h1398, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1400 | h1400
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1401 | h1401
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1402 | h1402
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1403 | h1403
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1404 | h1404
                          · rcases h3bigk with h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1332, hc13, hc35, hlam, hphi, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h3, hlam, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1131, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1332, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1392, hlam, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1396, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1398, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              rcases p1405_3 (m.d 0 3) (by simp) with h1416 | h1416
                              · linarith only [h1416, h3, hlam]
                              · rcases p1405_3 (m.d 1 3) (by simp) with h1418 | h1418
                                · linarith only [h1392, h1418, hlam]
                                · rcases p1405_3 (m.d 2 3) (by simp) with h1420 | h1420
                                  · rcases p1405_3 (m.d 3 4) (by simp) with h1421 | h1421
                                    · linarith only [h1401, h1421, hlam]
                                    · linarith only [h1131, h1421, hlam]
                                  · linarith only [h1420, h3, hlam]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              rcases p1405_3 (m.d 0 3) (by simp) with h1425 | h1425
                              · linarith only [h1425, h3, hlam]
                              · linarith only [h1, h1425, hlam]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1, h1131, h1392, hc12, hc23, hlam, hphi, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1, h1332, h1392, hc12, hc23, hlam, hphi, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1, h1392, hc12, hlam, hphi, ht23, ht34, p1405_1, u4elo3]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1392, hc12, hlam, hphi, ht23, ht34, p1405_1, u4elo3]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1401, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1, h1332, h1392, h1401, hc12, hlam, hphi, ht23, ht34, p1405_1, u4elo2]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1, h1392, h1402, hc12, hc23, hlam, hphi, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1392, h1402, hc12, hc23, hlam, hphi, p1405_1]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1402, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [h1404, hlam, p1405_0]
                            · have p1405_0 := h1405c.1
                              have p1405_1 := h1405c.2.1
                              have p1405_2 := h1405c.2.2.1
                              have p1405_3 := h1405c.2.2.2
                              linarith only [hlam, p1405_0]
                          · linarith only [h1, h1131, h1392, h1404, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h1400, h1403, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1, h1131, h1392, h1401, h1402, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1401, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1391, h1400, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
          · linarith only [h0, h1446, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1448 | h1448
            · linarith only [h0, h1448, h778, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1450 | h1450
              · linarith only [h1, h1131, h1391, h1450, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1452 | h1452
                · linarith only [h1, h1332, h1452, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1454 | h1454
                  · linarith only [h1, h1131, h1391, h1446, h1454, hc12, hlam, hphi, ht23, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1456 | h1456
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1457 | h1457
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1458 | h1458
                        · linarith only [h1, h1131, h1391, h1446, h1458, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1458, h778, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h1, h1131, h1446, h1456, h1457, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1456, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_13_24_L_I_M_LI_x0_x0_x0_x0 m hb3 hb4 h0 h1 h2 h3
  · exact r1l7_13_24_L_I_M_LI_x0_x0_x0_x1 m hb3 hb4 h0 h1 h2 h3

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_13_24_L_I_M_LI_x0_x0_x0 m hb3 hb4 h0 h1 h2
  · exact r1l7_13_24_L_I_M_LI_x0_x0_x1 m hb3 hb4 h0 h1 h2

end R2N4
