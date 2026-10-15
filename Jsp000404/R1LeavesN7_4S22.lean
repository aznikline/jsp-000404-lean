import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 3 4 (by decide) (by decide) with h16985 | h16985
  · linarith only [h14856, h14857, h16985, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h16987 | h16987
    · rcases m.htr 0 4 5 (by decide) (by decide) with h16988 | h16988
      · rcases m.htr 1 2 3 (by decide) (by decide) with h16989 | h16989
        · rcases m.htr 1 2 4 (by decide) (by decide) with h16990 | h16990
          · rcases m.htr 1 2 5 (by decide) (by decide) with h16991 | h16991
            · rcases m.htr 1 3 4 (by decide) (by decide) with h16992 | h16992
              · rcases m.htr 1 3 5 (by decide) (by decide) with h16993 | h16993
                · rcases m.htr 1 4 5 (by decide) (by decide) with h16994 | h16994
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h16995 | h16995
                    · linarith only [h13812, h14856, h14857, h16985, h16987, h16990, h16995, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h16997 | h16997
                      · linarith only [h14856, h14857, h16989, h16992, h16995, h16997, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h14856, h14857, h16987, h16989, h16992, h16995, h16997, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h12794, h16988, h16994, hlam]
                · linarith only [h11385, h16987, h16993, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17002 | h17002
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17003 | h17003
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17004 | h17004
                    · linarith only [h14856, h14857, h16990, h16992, h17004, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17006 | h17006
                      · linarith only [h14856, h14857, h16990, h17006, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h14856, h14857, h16987, h16990, h17006, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h14856, h14857, h16990, h17003, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h14856, h14857, h16987, h16990, h17002, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h14857, h16990, h16991, hc02, hc25, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17012 | h17012
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17013 | h17013
              · linarith only [h16985, h16987, h16989, h16990, h17013, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17015 | h17015
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17016 | h17016
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17017 | h17017
                    · linarith only [h0, h14856, h16990, h17013, h17017, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17019 | h17019
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17020 | h17020
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17021 | h17021
                          · rcases h1bigk with h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c | h17022c
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h0, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h11385, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h12794, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h13812, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h16990, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h13812, h16990, h17015, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h16990, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h13812, h16990, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h16989, h16990, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h16989, hlam, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h17013, hlam, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h13812, h16989, h16990, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              rcases p17022_3 (m.d 0 1) (by simp) with h17038 | h17038
                              · linarith only [h17038, hlam, p17022_0]
                              · rcases p17022_3 (m.d 1 2) (by simp) with h17040 | h17040
                                · linarith only [h16990, h17040, hlam]
                                · linarith only [h0, h17040, hlam]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h0, h14856, h16990, h17017, h17019, h17021, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h11385, h16990, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h13812, h16990, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h16989, h16990, h17015, h17017, hc01, hc34, hlam, hphi, ht12, ht23, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h17012, hlam, p17022_1]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h17015, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [h17016, hlam, p17022_0]
                            · have p17022_0 := h17022c.1
                              have p17022_1 := h17022c.2.1
                              have p17022_2 := h17022c.2.2.1
                              have p17022_3 := h17022c.2.2.2
                              linarith only [hlam, p17022_0]
                          · linarith only [h0, h16990, h17017, h17021, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h14856, h16988, h16990, h17019, h17020, hc05, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h11385, h16987, h16989, h16990, h17017, h17019, hc23, hc34, hlam, hphi]
                  · linarith only [h11385, h12794, h16987, h16988, h17013, h17016, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11385, h16987, h17015, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17057 | h17057
              · linarith only [h16985, h16987, h16989, h16990, h17057, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17059 | h17059
                · linarith only [h16989, h17012, h17059, hlam]
                · linarith only [h11385, h16987, h17059, hlam]
        · linarith only [h0, h14856, h16989, hlam]
      · linarith only [h14856, h14857, h16987, h16988, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h17064 | h17064
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17065 | h17065
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17066 | h17066
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17067 | h17067
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17068 | h17068
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17069 | h17069
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17070 | h17070
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17071 | h17071
                    · linarith only [h14856, h14857, h16985, h17066, h17071, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17073 | h17073
                      · linarith only [h14856, h14857, h16987, h17065, h17068, h17071, h17073, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17075 | h17075
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17076 | h17076
                          · rcases h1bigk with h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c | h17077c
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h0, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h11385, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h12794, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h13812, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              rcases p17077_3 (m.d 0 1) (by simp) with h17083 | h17083
                              · linarith only [h17083, hlam, p17077_0]
                              · rcases p17077_3 (m.d 1 2) (by simp) with h17085 | h17085
                                · rcases p17077_3 (m.d 1 3) (by simp) with h17086 | h17086
                                  · linarith only [h17065, h17086, hlam]
                                  · linarith only [h11385, h17086, hlam]
                                · linarith only [h17085, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h14857, h17068, h17071, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h14856, h14857, h17068, h17071, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h11385, h16987, h17069, hc01, hc12, hlam, hphi, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              rcases p17077_3 (m.d 0 1) (by simp) with h17094 | h17094
                              · linarith only [h17094, hlam, p17077_0]
                              · rcases p17077_3 (m.d 1 2) (by simp) with h17096 | h17096
                                · rcases p17077_3 (m.d 1 3) (by simp) with h17097 | h17097
                                  · rcases p17077_3 (m.d 1 4) (by simp) with h17098 | h17098
                                    · linarith only [h17068, h17098, hlam]
                                    · linarith only [h12794, h17098, hlam]
                                  · linarith only [h17097, hlam, p17077_0]
                                · linarith only [h0, h17096, hlam]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h17065, hlam, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h14856, h14857, h17068, h17071, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h11385, h16987, h17065, h17069, hc01, hc12, hlam, hphi, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              rcases p17077_3 (m.d 0 1) (by simp) with h17107 | h17107
                              · linarith only [h17107, hlam, p17077_0]
                              · rcases p17077_3 (m.d 1 2) (by simp) with h17109 | h17109
                                · rcases p17077_3 (m.d 1 3) (by simp) with h17110 | h17110
                                  · rcases p17077_3 (m.d 1 4) (by simp) with h17111 | h17111
                                    · rcases p17077_3 (m.d 1 5) (by simp) with h17112 | h17112
                                      · linarith only [h17070, h17112, hlam]
                                      · linarith only [h13812, h17112, hlam]
                                    · linarith only [h17111, hlam, p17077_0]
                                  · linarith only [h11385, h17110, hlam]
                                · linarith only [h0, h17109, hlam]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h17066, hlam, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h17068, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h11385, h16987, h17069, hc01, hc14, hlam, hphi, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              rcases p17077_3 (m.d 0 1) (by simp) with h17122 | h17122
                              · linarith only [h17122, hlam, p17077_0]
                              · rcases p17077_3 (m.d 1 2) (by simp) with h17124 | h17124
                                · rcases p17077_3 (m.d 1 3) (by simp) with h17125 | h17125
                                  · rcases p17077_3 (m.d 1 4) (by simp) with h17126 | h17126
                                    · rcases p17077_3 (m.d 1 5) (by simp) with h17127 | h17127
                                      · rcases h3bigk with h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c | h17128c
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, hlam, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h16987, hc23, hc35, hlam, hphi, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h16985, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h16987, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, h17065, hc01, hc12, hlam, hphi, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          rcases p17128_3 (m.d 0 3) (by simp) with h17136 | h17136
                                          · linarith only [h11385, h17136, hlam]
                                          · linarith only [h14856, h17136, hlam]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, h16985, h17065, hc01, hc12, hlam, hphi, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, h16987, h17065, hc01, hc12, hlam, hphi, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h14856, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17065, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17071, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17073, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, hc01, hc34, hlam, hphi, ht12, ht23, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17068, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17065, h17068, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, h16987, h17065, h17068, hc01, hc12, hlam, hphi, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h11385, hc01, hc35, hlam, hphi, ht12, ht23, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17069, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17065, h17069, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17128_1]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [h17076, hlam, p17128_0]
                                        · have p17128_0 := h17128c.1
                                          have p17128_1 := h17128c.2.1
                                          have p17128_2 := h17128c.2.2.1
                                          have p17128_3 := h17128c.2.2.2
                                          linarith only [hlam, p17128_0]
                                      · linarith only [h17127, hlam, p17077_0]
                                    · linarith only [h12794, h17126, hlam]
                                  · linarith only [h11385, h17125, hlam]
                                · linarith only [h0, h17124, hlam]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h17067, hlam, p17077_1]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h17069, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [h17070, hlam, p17077_0]
                            · have p17077_0 := h17077c.1
                              have p17077_1 := h17077c.2.1
                              have p17077_2 := h17077c.2.2.1
                              have p17077_3 := h17077c.2.2.2
                              linarith only [hlam, p17077_0]
                          · linarith only [h14856, h14857, h17071, h17076, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h14856, h14857, h17064, h17075, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h12794, h16987, h17064, h17065, h17069, h17070, hc01, hc12, hlam, hphi]
                · linarith only [h11385, h16985, h17068, h17069, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17168 | h17168
                · linarith only [h11385, h16987, h17068, h17168, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17170 | h17170
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17171 | h17171
                    · linarith only [h14856, h14857, h17068, h17171, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17173 | h17173
                      · linarith only [h14856, h14857, h17066, h17168, h17173, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17175 | h17175
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17176 | h17176
                          · rcases h1bigk with h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c | h17177c
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h0, hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h11385, hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h12794, hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h13812, hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              rcases p17177_3 (m.d 0 1) (by simp) with h17183 | h17183
                              · linarith only [h17183, hlam, p17177_0]
                              · rcases p17177_3 (m.d 1 2) (by simp) with h17185 | h17185
                                · rcases p17177_3 (m.d 1 3) (by simp) with h17186 | h17186
                                  · linarith only [h17065, h17186, hlam]
                                  · linarith only [h11385, h17186, hlam]
                                · linarith only [h17185, hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h11385, hc01, hc12, hlam, hphi, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h14856, h14857, h17066, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h11385, h17168, hc01, hc12, hlam, hphi, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17168, hc01, hc35, hlam, hphi, ht12, ht23, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17065, hlam, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17068, hlam, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17168, hlam, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              rcases p17177_3 (m.d 0 1) (by simp) with h17199 | h17199
                              · linarith only [h17199, hlam, p17177_0]
                              · rcases p17177_3 (m.d 1 2) (by simp) with h17201 | h17201
                                · rcases p17177_3 (m.d 1 3) (by simp) with h17202 | h17202
                                  · linarith only [h17068, h17202, hlam]
                                  · linarith only [h11385, h17202, hlam]
                                · linarith only [h0, h17201, hlam]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17066, hlam, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h11385, hc01, hc14, hlam, hphi, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h11385, h17068, h17168, hc01, hc34, hlam, hphi, ht12, ht23, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              rcases p17177_3 (m.d 0 1) (by simp) with h17210 | h17210
                              · linarith only [h17210, hlam, p17177_0]
                              · rcases p17177_3 (m.d 1 2) (by simp) with h17212 | h17212
                                · rcases p17177_3 (m.d 1 3) (by simp) with h17213 | h17213
                                  · linarith only [h17168, h17213, hlam]
                                  · linarith only [h11385, h17213, hlam]
                                · linarith only [h0, h17212, hlam]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17067, hlam, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h11385, hc01, hc15, hlam, hphi, p17177_1]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [h17170, hlam, p17177_0]
                            · have p17177_0 := h17177c.1
                              have p17177_1 := h17177c.2.1
                              have p17177_2 := h17177c.2.2.1
                              have p17177_3 := h17177c.2.2.2
                              linarith only [hlam, p17177_0]
                          · linarith only [h12794, h17064, h17068, h17176, hlam]
                        · linarith only [h14857, h17064, h17175, hlam]
                  · linarith only [h14857, h17064, h17066, h17170, hlam]
            · linarith only [h14856, h14857, h17066, h17067, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17225 | h17225
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17226 | h17226
              · linarith only [h11385, h16985, h17065, h17066, h17226, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17228 | h17228
                · linarith only [h16987, h17226, h17228, hc03, hc34, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17230 | h17230
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17231 | h17231
                    · linarith only [h11385, h17226, h17231, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17233 | h17233
                      · linarith only [h0, h11385, h14856, h17066, h17228, h17231, h17233, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17235 | h17235
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17236 | h17236
                          · rcases h1bigk with h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c | h17237c
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h0, hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h11385, hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h12794, hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h13812, hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17066, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h11385, h17066, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17066, hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h13812, h17066, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17228, hc01, hc35, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17065, hlam, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17226, hlam, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17228, hlam, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              rcases p17237_3 (m.d 0 1) (by simp) with h17253 | h17253
                              · linarith only [h17253, hlam, p17237_0]
                              · rcases p17237_3 (m.d 1 2) (by simp) with h17255 | h17255
                                · linarith only [h17066, h17255, hlam]
                                · linarith only [h0, h17255, hlam]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h0, h14856, h17066, h17231, hc23, hc34, hlam, hphi, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h11385, h17066, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h11385, h17066, h17228, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17066, h17225, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17225, hlam, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h11385, h17066, h17225, h17231, hc01, hc34, hlam, hphi, ht12, ht23, p17237_1]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [h17230, hlam, p17237_0]
                            · have p17237_0 := h17237c.1
                              have p17237_1 := h17237c.2.1
                              have p17237_2 := h17237c.2.2.1
                              have p17237_3 := h17237c.2.2.2
                              linarith only [hlam, p17237_0]
                          · linarith only [h17066, h17225, h17231, h17235, h17236, hlam]
                        · linarith only [h0, h17066, h17235, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h12794, h13812, h17064, h17066, h17225, h17230, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17270 | h17270
              · linarith only [h11385, h16985, h17065, h17066, h17270, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17272 | h17272
                · linarith only [h11385, h16987, h17065, h17066, h17272, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17274 | h17274
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17275 | h17275
                    · linarith only [h0, h14856, h17066, h17270, h17275, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17277 | h17277
                      · linarith only [h11385, h17272, h17277, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17279 | h17279
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17280 | h17280
                          · rcases h1bigk with h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c | h17281c
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h0, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h11385, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h12794, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h13812, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17225, h17275, h17279, hc01, hc34, hlam, hphi, ht12, ht23, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17225, h17275, h17279, hc13, hc34, hlam, hphi, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17066, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17225, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17065, h17225, h17275, h17279, hc01, hc34, hlam, hphi, ht12, ht23, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17065, hlam, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17270, hlam, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17272, hlam, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              rcases p17281_3 (m.d 0 1) (by simp) with h17297 | h17297
                              · linarith only [h17297, hlam, p17281_0]
                              · rcases p17281_3 (m.d 1 2) (by simp) with h17299 | h17299
                                · linarith only [h17066, h17299, hlam]
                                · linarith only [h0, h17299, hlam]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h11385, hc01, hc14, hlam, hphi, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h11385, h17065, h17066, h17225, h17275, hc01, hc34, hlam, hphi, ht12, ht23, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              rcases p17281_3 (m.d 0 1) (by simp) with h17306 | h17306
                              · linarith only [h17306, hlam, p17281_0]
                              · rcases p17281_3 (m.d 1 2) (by simp) with h17308 | h17308
                                · linarith only [h17225, h17308, hlam]
                                · linarith only [h0, h17308, hlam]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h11385, h17065, hc01, hc15, hlam, hphi, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h11385, h17272, h17280, hc01, hc34, hlam, hphi, ht12, ht23, p17281_1]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [h17274, hlam, p17281_0]
                            · have p17281_0 := h17281c.1
                              have p17281_1 := h17281c.2.1
                              have p17281_2 := h17281c.2.2.1
                              have p17281_3 := h17281c.2.2.2
                              linarith only [hlam, p17281_0]
                          · linarith only [h14856, h14857, h17275, h17280, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h11385, h17064, h17065, h17066, h17279, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h12794, h17064, h17274, hlam]
        · linarith only [h0, h14856, h17065, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17319 | h17319
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17320 | h17320
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17321 | h17321
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17322 | h17322
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17323 | h17323
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17324 | h17324
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17325 | h17325
                    · linarith only [h14856, h14857, h16985, h17064, h17319, h17322, h17324, h17325, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17327 | h17327
                      · linarith only [h11385, h14856, h14857, h16987, h17327, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17329 | h17329
                        · linarith only [h14856, h14857, h17064, h17319, h17322, h17325, h17329, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h14856, h14857, h17329, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h14856, h14857, h17320, h17324, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h11385, h16985, h17322, h17323, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17334 | h17334
                · linarith only [h11385, h16987, h17322, h17334, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17336 | h17336
                  · linarith only [h14856, h14857, h17064, h17322, h17336, hc23, hc34, hlam, hphi]
                  · linarith only [h14856, h14857, h17320, h17336, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h14856, h14857, h17320, h17321, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17340 | h17340
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17341 | h17341
              · linarith only [h11385, h16985, h17319, h17320, h17341, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17343 | h17343
                · linarith only [h11385, h16987, h17341, h17343, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17345 | h17345
                  · linarith only [h14856, h14857, h17064, h17341, h17345, hc23, hc34, hlam, hphi]
                  · linarith only [h17320, h17340, h17345, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17348 | h17348
              · linarith only [h11385, h16985, h17319, h17340, h17348, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17350 | h17350
                · linarith only [h11385, h16987, h17348, h17350, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17352 | h17352
                  · linarith only [h14856, h14857, h17064, h17348, h17352, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17354 | h17354
                    · linarith only [h0, h14856, h17320, h17352, h17354, hc34, hc45, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17356 | h17356
                      · linarith only [h11385, h17350, h17356, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17358 | h17358
                        · linarith only [h0, h14856, h17320, h17352, h17354, h17358, hc23, hc34, hlam, hphi]
                        · linarith only [h14856, h14857, h17358, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h14856, h14857, h17319, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 2 4 (by decide) (by decide) with h14857 | h14857
  · exact r1l7_11_23_L_I_H_I_s15_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857
  · exact r1l7_11_23_L_I_H_I_s15_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857

set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  exact r1l7_11_23_L_I_H_I_s15 m hb1 hb3 h0 h11385 h12794 h13812 h14856

end R2N4
