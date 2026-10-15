import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S30

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6964000 in
set_option maxHeartbeats 6964000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s17 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  rcases m.htr 0 2 4 (by decide) (by decide) with h19111 | h19111
  · exact r1l7_11_13_25_L_I_L_I_H_I_s18 m hb1 hb3 hb5 h0 h14799 h16563 h17994 h19110 h19111
  · rcases m.htr 0 2 5 (by decide) (by decide) with h22035 | h22035
    · rcases m.htr 0 3 4 (by decide) (by decide) with h22036 | h22036
      · linarith only [h19110, h19111, h22036, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h22038 | h22038
        · rcases m.htr 0 4 5 (by decide) (by decide) with h22039 | h22039
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22040 | h22040
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22041 | h22041
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22042 | h22042
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22043 | h22043
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22044 | h22044
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22045 | h22045
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22046 | h22046
                        · linarith only [h17994, h19110, h19111, h22036, h22038, h22041, h22046, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22048 | h22048
                          · linarith only [h19110, h19111, h22040, h22043, h22046, h22048, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h19110, h19111, h22038, h22040, h22043, h22046, h22048, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h16563, h22039, h22045, hlam]
                    · linarith only [h0, h14799, h19110, h22038, h22044, hc01, hc12, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22053 | h22053
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22054 | h22054
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22055 | h22055
                        · linarith only [h16563, h19110, h19111, h22041, h22043, h22055, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22057 | h22057
                          · linarith only [h19110, h19111, h22041, h22057, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h19110, h19111, h22038, h22041, h22057, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h17994, h19111, h22039, h22041, h22043, h22053, h22054, hc02, hc34, hlam, hphi, ht23]
                    · linarith only [h19110, h19111, h22038, h22041, h22053, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h19111, h22041, h22042, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22063 | h22063
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22064 | h22064
                  · linarith only [h22036, h22038, h22040, h22041, h22064, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22066 | h22066
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22067 | h22067
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22068 | h22068
                        · linarith only [h0, h19110, h22041, h22064, h22068, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22070 | h22070
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22071 | h22071
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22072 | h22072
                              · rcases h1bigk with h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c | h22073c
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h0, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h14799, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h16563, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h17994, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22041, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h17994, h22041, h22066, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22041, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h17994, h22041, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22040, h22041, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22040, hlam, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22064, hlam, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h17994, h22040, h22041, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  rcases p22073_3 (m.d 0 1) (by simp) with h22089 | h22089
                                  · linarith only [h22089, hlam, p22073_0]
                                  · rcases p22073_3 (m.d 1 2) (by simp) with h22091 | h22091
                                    · linarith only [h22041, h22091, hlam]
                                    · linarith only [h0, h22091, hlam]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h14799, hc01, hc14, hlam, hphi, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h17994, h22041, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22040, h22041, h22066, h22068, hc01, hc34, hlam, hphi, ht12, ht23, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22063, hlam, p22073_1]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22066, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [h22067, hlam, p22073_0]
                                · have p22073_0 := h22073c.1
                                  have p22073_1 := h22073c.2.1
                                  have p22073_2 := h22073c.2.2.1
                                  have p22073_3 := h22073c.2.2.2
                                  linarith only [hlam, p22073_0]
                              · linarith only [h0, h19110, h22041, h22068, h22072, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h19110, h22039, h22041, h22070, h22071, hc05, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h19110, h22038, h22041, h22068, h22070, hc23, hc34, hlam, hphi]
                      · linarith only [h16563, h22039, h22067, hlam]
                    · linarith only [h14799, h22038, h22066, hlam]
                · linarith only [h0, h22035, h22063, hlam]
            · linarith only [h0, h19110, h22040, hlam]
          · linarith only [h19110, h19111, h22038, h22039, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h22111 | h22111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22112 | h22112
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22113 | h22113
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22114 | h22114
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22115 | h22115
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22116 | h22116
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22117 | h22117
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22118 | h22118
                        · linarith only [h14799, h19110, h19111, h22036, h22113, h22118, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22120 | h22120
                          · linarith only [h14799, h19110, h19111, h22038, h22115, h22118, h22120, hc01, hc13, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22122 | h22122
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22123 | h22123
                              · rcases h1bigk with h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c | h22124c
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h0, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h14799, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h16563, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h17994, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  rcases p22124_3 (m.d 0 1) (by simp) with h22130 | h22130
                                  · linarith only [h22130, hlam, p22124_0]
                                  · rcases p22124_3 (m.d 1 2) (by simp) with h22132 | h22132
                                    · rcases p22124_3 (m.d 1 3) (by simp) with h22133 | h22133
                                      · linarith only [h22112, h22133, hlam]
                                      · linarith only [h14799, h22133, hlam]
                                    · linarith only [h22132, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h19111, h22035, h22115, h22118, h22120, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h16563, hc01, hc12, hlam, hphi, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h14799, h22038, h22116, hc01, hc12, hlam, hphi, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  rcases p22124_3 (m.d 0 1) (by simp) with h22141 | h22141
                                  · linarith only [h22141, hlam, p22124_0]
                                  · rcases p22124_3 (m.d 1 2) (by simp) with h22143 | h22143
                                    · rcases p22124_3 (m.d 1 3) (by simp) with h22144 | h22144
                                      · rcases p22124_3 (m.d 1 4) (by simp) with h22145 | h22145
                                        · linarith only [h22115, h22145, hlam]
                                        · linarith only [h16563, h22145, hlam]
                                      · linarith only [h22144, hlam, p22124_0]
                                    · linarith only [h0, h22143, hlam]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h22112, hlam, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h19111, h22035, h22115, h22118, h22120, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h14799, h22038, h22112, h22116, hc01, hc12, hlam, hphi, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  rcases p22124_3 (m.d 0 1) (by simp) with h22154 | h22154
                                  · linarith only [h22154, hlam, p22124_0]
                                  · rcases p22124_3 (m.d 1 2) (by simp) with h22156 | h22156
                                    · rcases p22124_3 (m.d 1 3) (by simp) with h22157 | h22157
                                      · rcases p22124_3 (m.d 1 4) (by simp) with h22158 | h22158
                                        · rcases p22124_3 (m.d 1 5) (by simp) with h22159 | h22159
                                          · linarith only [h22117, h22159, hlam]
                                          · linarith only [h17994, h22159, hlam]
                                        · linarith only [h22158, hlam, p22124_0]
                                      · linarith only [h14799, h22157, hlam]
                                    · linarith only [h0, h22156, hlam]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h22113, hlam, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h22115, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h14799, h22038, h22116, hc01, hc14, hlam, hphi, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  rcases p22124_3 (m.d 0 1) (by simp) with h22169 | h22169
                                  · linarith only [h22169, hlam, p22124_0]
                                  · rcases p22124_3 (m.d 1 2) (by simp) with h22171 | h22171
                                    · rcases p22124_3 (m.d 1 3) (by simp) with h22172 | h22172
                                      · rcases p22124_3 (m.d 1 4) (by simp) with h22173 | h22173
                                        · rcases p22124_3 (m.d 1 5) (by simp) with h22174 | h22174
                                          · rcases h3bigk with h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c | h22175c
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h14799, hlam, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22038, hc23, hc35, hlam, hphi, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22036, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22038, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              rcases p22175_3 (m.d 0 3) (by simp) with h22181 | h22181
                                              · linarith only [h14799, h22181, hlam]
                                              · rcases p22175_3 (m.d 1 3) (by simp) with h22183 | h22183
                                                · rcases p22175_3 (m.d 2 3) (by simp) with h22184 | h22184
                                                  · linarith only [h22112, h22184, hlam]
                                                  · rcases p22175_3 (m.d 3 4) (by simp) with h22186 | h22186
                                                    · linarith only [h22115, h22186, hlam]
                                                    · linarith only [h22036, h22186, hlam]
                                                · linarith only [h14799, h22183, hlam]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h19111, h22035, h22115, h22118, h22120, hlam, p22175_2]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h19111, h22035, h22118, h22120, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h14799, h22038, h22112, hc01, hc12, hlam, hphi, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h19110, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22112, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22118, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22120, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h14799, h22112, h22115, hc01, hc12, hlam, hphi, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22115, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              rcases p22175_3 (m.d 0 3) (by simp) with h22201 | h22201
                                              · linarith only [h22036, h22201, hlam]
                                              · linarith only [h19110, h22201, hlam]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h14799, h22038, h22112, h22115, hc01, hc12, hlam, hphi, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h14799, h22112, h22116, hc01, hc12, hlam, hphi, p22175_1]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22116, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              rcases p22175_3 (m.d 0 3) (by simp) with h22208 | h22208
                                              · linarith only [h22038, h22208, hlam]
                                              · linarith only [h19110, h22208, hlam]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [h22123, hlam, p22175_0]
                                            · have p22175_0 := h22175c.1
                                              have p22175_1 := h22175c.2.1
                                              have p22175_2 := h22175c.2.2.1
                                              have p22175_3 := h22175c.2.2.2
                                              linarith only [hlam, p22175_0]
                                          · linarith only [h22174, hlam, p22124_0]
                                        · linarith only [h16563, h22173, hlam]
                                      · linarith only [h14799, h22172, hlam]
                                    · linarith only [h0, h22171, hlam]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h22114, hlam, p22124_1]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h22116, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [h22117, hlam, p22124_0]
                                · have p22124_0 := h22124c.1
                                  have p22124_1 := h22124c.2.1
                                  have p22124_2 := h22124c.2.2.1
                                  have p22124_3 := h22124c.2.2.2
                                  linarith only [hlam, p22124_0]
                              · linarith only [h14799, h19111, h22035, h22036, h22122, h22123, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h19110, h19111, h22122, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h16563, h22036, h22111, h22112, h22115, h22117, hc01, hc12, hlam, hphi]
                    · linarith only [h19110, h19111, h22036, h22115, h22116, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22225 | h22225
                    · linarith only [h14799, h22038, h22115, h22225, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22227 | h22227
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22228 | h22228
                        · linarith only [h14799, h19110, h22115, h22228, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22230 | h22230
                          · linarith only [h14799, h19110, h19111, h22113, h22225, h22230, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22232 | h22232
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22233 | h22233
                              · rcases h1bigk with h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c | h22234c
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h0, hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h14799, hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h16563, hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h17994, hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  rcases p22234_3 (m.d 0 1) (by simp) with h22240 | h22240
                                  · linarith only [h22240, hlam, p22234_0]
                                  · rcases p22234_3 (m.d 1 2) (by simp) with h22242 | h22242
                                    · rcases p22234_3 (m.d 1 3) (by simp) with h22243 | h22243
                                      · linarith only [h22112, h22243, hlam]
                                      · linarith only [h14799, h22243, hlam]
                                    · linarith only [h22242, hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h16563, hc01, hc12, hlam, hphi, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h14799, h22225, hc01, hc12, hlam, hphi, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22225, hc01, hc35, hlam, hphi, ht12, ht23, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22112, hlam, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22115, hlam, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22225, hlam, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  rcases p22234_3 (m.d 0 1) (by simp) with h22256 | h22256
                                  · linarith only [h22256, hlam, p22234_0]
                                  · rcases p22234_3 (m.d 1 2) (by simp) with h22258 | h22258
                                    · rcases p22234_3 (m.d 1 3) (by simp) with h22259 | h22259
                                      · linarith only [h22115, h22259, hlam]
                                      · linarith only [h14799, h22259, hlam]
                                    · linarith only [h0, h22258, hlam]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22113, hlam, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h14799, hc01, hc14, hlam, hphi, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h14799, h22115, h22225, hc01, hc34, hlam, hphi, ht12, ht23, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  rcases p22234_3 (m.d 0 1) (by simp) with h22267 | h22267
                                  · linarith only [h22267, hlam, p22234_0]
                                  · rcases p22234_3 (m.d 1 2) (by simp) with h22269 | h22269
                                    · rcases p22234_3 (m.d 1 3) (by simp) with h22270 | h22270
                                      · linarith only [h22225, h22270, hlam]
                                      · linarith only [h14799, h22270, hlam]
                                    · linarith only [h0, h22269, hlam]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22114, hlam, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h14799, hc01, hc15, hlam, hphi, p22234_1]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [h22227, hlam, p22234_0]
                                · have p22234_0 := h22234c.1
                                  have p22234_1 := h22234c.2.1
                                  have p22234_2 := h22234c.2.2.1
                                  have p22234_3 := h22234c.2.2.2
                                  linarith only [hlam, p22234_0]
                              · linarith only [h19111, h22035, h22113, h22115, h22232, h22233, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h19111, h22035, h22230, h22232, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h19111, h22035, h22111, h22113, h22227, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h19110, h19111, h22113, h22114, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22282 | h22282
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22283 | h22283
                  · linarith only [h14799, h22036, h22112, h22113, h22283, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22285 | h22285
                    · linarith only [h22038, h22283, h22285, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22287 | h22287
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22288 | h22288
                        · linarith only [h14799, h22283, h22288, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22290 | h22290
                          · linarith only [h0, h14799, h19110, h22113, h22285, h22288, h22290, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22292 | h22292
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22293 | h22293
                              · rcases h1bigk with h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c | h22294c
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h0, hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h14799, hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h16563, hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h17994, hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22113, h22288, hc01, hc34, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h14799, h22113, h22288, hc01, hc34, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22113, hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h17994, h22113, h22288, hc01, hc34, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22285, hc01, hc35, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22112, hlam, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22283, hlam, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22285, hlam, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  rcases p22294_3 (m.d 0 1) (by simp) with h22310 | h22310
                                  · linarith only [h22310, hlam, p22294_0]
                                  · rcases p22294_3 (m.d 1 2) (by simp) with h22312 | h22312
                                    · linarith only [h22113, h22312, hlam]
                                    · linarith only [h0, h22312, hlam]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h14799, hc01, hc14, hlam, hphi, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h14799, h22113, h22285, h22288, hc01, hc34, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22113, h22282, h22288, hc01, hc34, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22282, hlam, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h14799, h22113, h22282, h22288, hc01, hc34, hlam, hphi, ht12, ht23, p22294_1]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [h22287, hlam, p22294_0]
                                · have p22294_0 := h22294c.1
                                  have p22294_1 := h22294c.2.1
                                  have p22294_2 := h22294c.2.2.1
                                  have p22294_3 := h22294c.2.2.2
                                  linarith only [hlam, p22294_0]
                              · linarith only [h0, h22035, h22113, h22288, h22292, h22293, hlam]
                            · linarith only [h0, h22035, h22113, h22290, h22292, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h16563, h22111, h22287, hlam]
                · linarith only [h0, h22035, h22282, hlam]
            · linarith only [h0, h19110, h22112, hlam]
          · linarith only [h19111, h22035, h22111, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h22330 | h22330
      · linarith only [h19110, h19111, h22330, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h22332 | h22332
        · linarith only [h19110, h22035, h22332, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h22334 | h22334
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22335 | h22335
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22336 | h22336
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22337 | h22337
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22338 | h22338
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22339 | h22339
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22340 | h22340
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22341 | h22341
                        · linarith only [h19110, h19111, h22330, h22336, h22341, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22343 | h22343
                          · linarith only [h14799, h19110, h19111, h22332, h22335, h22338, h22341, h22343, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22345 | h22345
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22346 | h22346
                              · rcases h1bigk with h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c | h22347c
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h0, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h14799, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h16563, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h17994, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  rcases p22347_3 (m.d 0 1) (by simp) with h22353 | h22353
                                  · linarith only [h22353, hlam, p22347_0]
                                  · rcases p22347_3 (m.d 1 2) (by simp) with h22355 | h22355
                                    · rcases p22347_3 (m.d 1 3) (by simp) with h22356 | h22356
                                      · linarith only [h22335, h22356, hlam]
                                      · linarith only [h14799, h22356, hlam]
                                    · linarith only [h22355, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22035, h22338, h22341, h22345, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h16563, hc01, hc12, hlam, hphi, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h19110, h22035, h22339, h22343, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  rcases p22347_3 (m.d 0 1) (by simp) with h22364 | h22364
                                  · linarith only [h22364, hlam, p22347_0]
                                  · rcases p22347_3 (m.d 1 2) (by simp) with h22366 | h22366
                                    · rcases p22347_3 (m.d 1 3) (by simp) with h22367 | h22367
                                      · rcases p22347_3 (m.d 1 4) (by simp) with h22368 | h22368
                                        · linarith only [h22338, h22368, hlam]
                                        · linarith only [h16563, h22368, hlam]
                                      · linarith only [h22367, hlam, p22347_0]
                                    · linarith only [h0, h22366, hlam]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22335, hlam, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h19110, h22035, h22338, h22341, h22345, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h19110, h22035, h22335, h22339, h22343, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  rcases p22347_3 (m.d 0 1) (by simp) with h22377 | h22377
                                  · linarith only [h22377, hlam, p22347_0]
                                  · rcases p22347_3 (m.d 1 2) (by simp) with h22379 | h22379
                                    · rcases p22347_3 (m.d 1 3) (by simp) with h22380 | h22380
                                      · rcases p22347_3 (m.d 1 4) (by simp) with h22381 | h22381
                                        · rcases p22347_3 (m.d 1 5) (by simp) with h22382 | h22382
                                          · linarith only [h22340, h22382, hlam]
                                          · linarith only [h17994, h22382, hlam]
                                        · linarith only [h22381, hlam, p22347_0]
                                      · linarith only [h14799, h22380, hlam]
                                    · linarith only [h0, h22379, hlam]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22336, hlam, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22338, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h19110, h22035, h22339, h22343, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  rcases p22347_3 (m.d 0 1) (by simp) with h22392 | h22392
                                  · linarith only [h22392, hlam, p22347_0]
                                  · rcases p22347_3 (m.d 1 2) (by simp) with h22394 | h22394
                                    · rcases p22347_3 (m.d 1 3) (by simp) with h22395 | h22395
                                      · rcases p22347_3 (m.d 1 4) (by simp) with h22396 | h22396
                                        · rcases p22347_3 (m.d 1 5) (by simp) with h22397 | h22397
                                          · rcases h3bigk with h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c | h22398c
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h14799, hlam, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h19110, h22035, h22341, h22345, hc23, hc34, hlam, hphi, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22330, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22332, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              rcases p22398_3 (m.d 0 3) (by simp) with h22404 | h22404
                                              · linarith only [h14799, h22404, hlam]
                                              · rcases p22398_3 (m.d 1 3) (by simp) with h22406 | h22406
                                                · rcases p22398_3 (m.d 2 3) (by simp) with h22407 | h22407
                                                  · linarith only [h22335, h22407, hlam]
                                                  · rcases p22398_3 (m.d 3 4) (by simp) with h22409 | h22409
                                                    · linarith only [h22338, h22409, hlam]
                                                    · linarith only [h22330, h22409, hlam]
                                                · linarith only [h14799, h22406, hlam]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h19110, h22035, h22338, h22341, h22345, hlam, p22398_2]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h0, h22035, h22335, h22341, h22345, hc01, hc12, hlam, hphi, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h14799, h22332, h22335, hc01, hc12, hlam, hphi, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h19110, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22335, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22341, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22343, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h14799, h22335, h22338, hc01, hc12, hlam, hphi, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22338, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              rcases p22398_3 (m.d 0 3) (by simp) with h22424 | h22424
                                              · linarith only [h22330, h22424, hlam]
                                              · linarith only [h19110, h22424, hlam]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h19110, h22035, h22335, h22338, h22343, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h14799, h22335, h22339, hc01, hc12, hlam, hphi, p22398_1]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22339, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              rcases p22398_3 (m.d 0 3) (by simp) with h22431 | h22431
                                              · linarith only [h22332, h22431, hlam]
                                              · linarith only [h19110, h22431, hlam]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [h22346, hlam, p22398_0]
                                            · have p22398_0 := h22398c.1
                                              have p22398_1 := h22398c.2.1
                                              have p22398_2 := h22398c.2.2.1
                                              have p22398_3 := h22398c.2.2.2
                                              linarith only [hlam, p22398_0]
                                          · linarith only [h22397, hlam, p22347_0]
                                        · linarith only [h16563, h22396, hlam]
                                      · linarith only [h14799, h22395, hlam]
                                    · linarith only [h0, h22394, hlam]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22337, hlam, p22347_1]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22339, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [h22340, hlam, p22347_0]
                                · have p22347_0 := h22347c.1
                                  have p22347_1 := h22347c.2.1
                                  have p22347_2 := h22347c.2.2.1
                                  have p22347_3 := h22347c.2.2.2
                                  linarith only [hlam, p22347_0]
                              · linarith only [h14799, h16563, h22330, h22334, h22335, h22338, h22346, hc01, hc12, hlam, hphi]
                            · linarith only [h19110, h19111, h22345, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h16563, h22330, h22334, h22335, h22338, h22340, hc01, hc12, hlam, hphi]
                    · linarith only [h19110, h19111, h22330, h22338, h22339, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22448 | h22448
                    · linarith only [h14799, h22332, h22338, h22448, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22450 | h22450
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22451 | h22451
                        · linarith only [h19110, h19111, h22336, h22338, h22451, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22453 | h22453
                          · linarith only [h19110, h22035, h22337, h22448, h22453, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22455 | h22455
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22456 | h22456
                              · rcases h1bigk with h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c | h22457c
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h0, hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h14799, hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h16563, hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h17994, hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  rcases p22457_3 (m.d 0 1) (by simp) with h22463 | h22463
                                  · linarith only [h22463, hlam, p22457_0]
                                  · rcases p22457_3 (m.d 1 2) (by simp) with h22465 | h22465
                                    · rcases p22457_3 (m.d 1 3) (by simp) with h22466 | h22466
                                      · linarith only [h22335, h22466, hlam]
                                      · linarith only [h14799, h22466, hlam]
                                    · linarith only [h22465, hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h19110, h22035, h22337, h22450, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h19110, h22035, h22337, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22338, hc01, hc34, hlam, hphi, ht12, ht23, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22335, hlam, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22338, hlam, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22448, hlam, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  rcases p22457_3 (m.d 0 1) (by simp) with h22479 | h22479
                                  · linarith only [h22479, hlam, p22457_0]
                                  · rcases p22457_3 (m.d 1 2) (by simp) with h22481 | h22481
                                    · rcases p22457_3 (m.d 1 3) (by simp) with h22482 | h22482
                                      · linarith only [h22338, h22482, hlam]
                                      · linarith only [h14799, h22482, hlam]
                                    · linarith only [h0, h22481, hlam]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22336, hlam, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h14799, hc01, hc14, hlam, hphi, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h19110, h22035, h22337, h22338, hc23, hc34, hlam, hphi, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  rcases p22457_3 (m.d 0 1) (by simp) with h22490 | h22490
                                  · linarith only [h22490, hlam, p22457_0]
                                  · rcases p22457_3 (m.d 1 2) (by simp) with h22492 | h22492
                                    · rcases p22457_3 (m.d 1 3) (by simp) with h22493 | h22493
                                      · linarith only [h22448, h22493, hlam]
                                      · linarith only [h14799, h22493, hlam]
                                    · linarith only [h0, h22492, hlam]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22337, hlam, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h14799, hc01, hc15, hlam, hphi, p22457_1]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [h22450, hlam, p22457_0]
                                · have p22457_0 := h22457c.1
                                  have p22457_1 := h22457c.2.1
                                  have p22457_2 := h22457c.2.2.1
                                  have p22457_3 := h22457c.2.2.2
                                  linarith only [hlam, p22457_0]
                              · linarith only [h16563, h22334, h22338, h22456, hlam]
                            · linarith only [h19111, h22334, h22455, hlam]
                      · linarith only [h19111, h22334, h22336, h22450, hlam]
                · linarith only [h19110, h19111, h22336, h22337, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22505 | h22505
                · linarith only [h19110, h22035, h22336, h22505, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22507 | h22507
                  · linarith only [h14799, h22330, h22335, h22336, h22507, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22509 | h22509
                    · linarith only [h14799, h22332, h22507, h22509, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22511 | h22511
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22512 | h22512
                        · linarith only [h0, h19110, h22336, h22507, h22512, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22514 | h22514
                          · linarith only [h19110, h22332, h22514, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22516 | h22516
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h22517 | h22517
                              · rcases h1bigk with h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c | h22518c
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h0, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h14799, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h16563, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h17994, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22505, h22512, h22516, hc01, hc34, hlam, hphi, ht12, ht23, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h14799, h22505, h22512, h22516, hc01, hc34, hlam, hphi, ht12, ht23, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22336, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22505, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22335, h22505, h22512, h22516, hc01, hc34, hlam, hphi, ht12, ht23, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22335, hlam, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22507, hlam, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22509, hlam, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  rcases p22518_3 (m.d 0 1) (by simp) with h22534 | h22534
                                  · linarith only [h22534, hlam, p22518_0]
                                  · rcases p22518_3 (m.d 1 2) (by simp) with h22536 | h22536
                                    · linarith only [h22336, h22536, hlam]
                                    · linarith only [h0, h22536, hlam]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h14799, hc01, hc14, hlam, hphi, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h17994, h22336, h22512, hc01, hc34, hlam, hphi, ht12, ht23, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  rcases p22518_3 (m.d 0 1) (by simp) with h22543 | h22543
                                  · linarith only [h22543, hlam, p22518_0]
                                  · rcases p22518_3 (m.d 1 2) (by simp) with h22545 | h22545
                                    · linarith only [h22505, h22545, hlam]
                                    · linarith only [h0, h22545, hlam]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h14799, h22335, hc01, hc15, hlam, hphi, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h14799, hc01, hc15, hlam, hphi, p22518_1]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [h22511, hlam, p22518_0]
                                · have p22518_0 := h22518c.1
                                  have p22518_1 := h22518c.2.1
                                  have p22518_2 := h22518c.2.2.1
                                  have p22518_3 := h22518c.2.2.2
                                  linarith only [hlam, p22518_0]
                              · linarith only [h19110, h19111, h22512, h22517, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h14799, h22334, h22335, h22336, h22516, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h16563, h22334, h22511, hlam]
            · linarith only [h0, h19110, h22335, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22556 | h22556
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22557 | h22557
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22558 | h22558
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22559 | h22559
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22560 | h22560
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22561 | h22561
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22562 | h22562
                        · linarith only [h14799, h19110, h19111, h22330, h22334, h22556, h22559, h22561, h22562, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22564 | h22564
                          · linarith only [h19110, h19111, h22334, h22556, h22559, h22561, h22564, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22566 | h22566
                            · linarith only [h19110, h19111, h22334, h22562, h22566, hc23, hc34, hlam, hphi]
                            · linarith only [h19110, h19111, h22556, h22559, h22561, h22566, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h19110, h19111, h22557, h22561, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h14799, h22330, h22559, h22560, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22571 | h22571
                    · linarith only [h14799, h22332, h22559, h22571, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22573 | h22573
                      · linarith only [h19110, h19111, h22334, h22559, h22573, hc23, hc34, hlam, hphi]
                      · linarith only [h19110, h19111, h22557, h22573, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h19110, h19111, h22557, h22558, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22577 | h22577
                · linarith only [h19110, h22035, h22557, h22577, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h22579 | h22579
                  · linarith only [h14799, h22330, h22556, h22557, h22579, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22581 | h22581
                    · linarith only [h14799, h22332, h22579, h22581, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22583 | h22583
                      · linarith only [h19110, h19111, h22334, h22579, h22583, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22585 | h22585
                        · linarith only [h16563, h19110, h19111, h22583, h22585, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h22587 | h22587
                          · linarith only [h14799, h16563, h19110, h19111, h22332, h22583, h22587, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22589 | h22589
                            · linarith only [h0, h22557, h22583, h22585, h22589, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h19110, h19111, h22589, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h19110, h19111, h22556, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  exact r1l7_11_13_25_L_I_L_I_H_I_s17 m hb1 hb3 hb5 h0 h14799 h16563 h17994 h19110

end R2N4
