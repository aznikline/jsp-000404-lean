import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5868000 in
set_option maxHeartbeats 5868000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  rcases m.htr 0 2 4 (by decide) (by decide) with h8379 | h8379
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12 m hb1 hb2 hb4 hb5 h0 h6794 h7647 h8170 h8378 h8379
  · rcases m.htr 0 2 5 (by decide) (by decide) with h10991 | h10991
    · rcases m.htr 0 3 4 (by decide) (by decide) with h10992 | h10992
      · linarith only [h10992, h8378, h8379, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10994 | h10994
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10995 | h10995
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10996 | h10996
            · linarith only [h10991, h10996, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10998 | h10998
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10999 | h10999
                · linarith only [h10992, h10995, h10996, h10999, h6794, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11001 | h11001
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11002 | h11002
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11003 | h11003
                      · linarith only [h10999, h11001, h11003, h8378, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11005 | h11005
                        · linarith only [h0, h10996, h11003, h11005, h8378, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h10995, h10996, h11001, h11003, h11005, hc23, hc34, hlam, hphi]
                    · linarith only [h10994, h10995, h10996, h11001, h11002, h8170, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11009 | h11009
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11010 | h11010
                      · linarith only [h10999, h11010, h6794, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11012 | h11012
                        · linarith only [h0, h10996, h11001, h11010, h11012, h6794, h8378, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11014 | h11014
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11015 | h11015
                            · rcases h1bigk with h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c | h11016c
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h0, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h6794, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h7647, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h8170, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h11010, hc01, hc34, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h11010, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, hlam, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h11010, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11016_1, u5ehi1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h11001, hc01, hc35, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10995, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10999, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h11001, hlam, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                rcases p11016_3 (m.d 0 1) (by simp) with h11032 | h11032
                                · linarith only [h11032, hlam, p11016_0]
                                · rcases p11016_3 (m.d 1 2) (by simp) with h11034 | h11034
                                  · linarith only [h10996, h11034, hlam]
                                  · linarith only [h0, h11034, hlam]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h0, h10991, hc14, hlam, hphi, ht01, ht0b, ht5b, p11016_1, u5ehi2]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h11010, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h11001, h11010, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h10998, h11010, hc01, hc34, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10998, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h10996, h10998, h11010, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11016_1]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [h11009, hlam, p11016_0]
                              · have p11016_0 := h11016c.1
                                have p11016_1 := h11016c.2.1
                                have p11016_2 := h11016c.2.2.1
                                have p11016_3 := h11016c.2.2.2
                                linarith only [hlam, p11016_0]
                            · linarith only [h0, h10991, h10996, h11010, h11014, h11015, hlam]
                          · linarith only [h0, h10991, h10996, h11014, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h0, h10991, h10994, h10996, h11009, h7647, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h10991, h10998, hlam]
          · linarith only [h0, h10995, h8378, hlam]
        · linarith only [h10991, h10994, h8379, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h11052 | h11052
      · linarith only [h11052, h8378, h8379, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11054 | h11054
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11055 | h11055
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11056 | h11056
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11057 | h11057
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11058 | h11058
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11059 | h11059
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11060 | h11060
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11061 | h11061
                      · linarith only [h11052, h11056, h11061, h8378, h8379, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11063 | h11063
                        · linarith only [h11055, h11058, h11061, h11063, h8378, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11065 | h11065
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11066 | h11066
                            · rcases h1bigk with h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h0, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h6794, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h7647, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h8170, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                rcases p11067_3 (m.d 0 1) (by simp) with h11073 | h11073
                                · linarith only [h11073, hlam, p11067_0]
                                · rcases p11067_3 (m.d 1 2) (by simp) with h11075 | h11075
                                  · rcases p11067_3 (m.d 1 3) (by simp) with h11076 | h11076
                                    · linarith only [h11055, h11076, hlam]
                                    · linarith only [h11076, h6794, hlam]
                                  · linarith only [h11075, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h10991, h11058, h11061, h11065, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h10991, h11059, h11060, h11063, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h10991, h11059, h11063, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                rcases p11067_3 (m.d 0 1) (by simp) with h11084 | h11084
                                · linarith only [h11084, hlam, p11067_0]
                                · rcases p11067_3 (m.d 1 2) (by simp) with h11086 | h11086
                                  · rcases p11067_3 (m.d 1 3) (by simp) with h11087 | h11087
                                    · rcases p11067_3 (m.d 1 4) (by simp) with h11088 | h11088
                                      · linarith only [h11058, h11088, hlam]
                                      · linarith only [h11088, h7647, hlam]
                                    · linarith only [h11087, hlam, p11067_0]
                                  · linarith only [h0, h11086, hlam]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h11055, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h10991, h11059, h11060, h11063, h8378, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h10991, h11055, h11059, h11063, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                rcases p11067_3 (m.d 0 1) (by simp) with h11097 | h11097
                                · linarith only [h11097, hlam, p11067_0]
                                · rcases p11067_3 (m.d 1 2) (by simp) with h11099 | h11099
                                  · rcases p11067_3 (m.d 1 3) (by simp) with h11100 | h11100
                                    · rcases p11067_3 (m.d 1 4) (by simp) with h11101 | h11101
                                      · rcases p11067_3 (m.d 1 5) (by simp) with h11102 | h11102
                                        · linarith only [h11060, h11102, hlam]
                                        · linarith only [h11102, h8170, hlam]
                                      · linarith only [h11101, hlam, p11067_0]
                                    · linarith only [h11100, h6794, hlam]
                                  · linarith only [h0, h11099, hlam]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h11056, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h11058, hlam, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h10991, h11059, h11063, h8378, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11067_1]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                rcases p11067_3 (m.d 0 1) (by simp) with h11112 | h11112
                                · linarith only [h11112, hlam, p11067_0]
                                · rcases p11067_3 (m.d 1 2) (by simp) with h11114 | h11114
                                  · rcases p11067_3 (m.d 1 3) (by simp) with h11115 | h11115
                                    · rcases p11067_3 (m.d 1 4) (by simp) with h11116 | h11116
                                      · rcases p11067_3 (m.d 1 5) (by simp) with h11117 | h11117
                                        · rcases h2bigk with h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c | h11118c
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h0, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h10991, h11061, h11065, hc23, hc34, hlam, hphi, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h8379, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h10991, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            rcases p11118_3 (m.d 0 2) (by simp) with h11124 | h11124
                                            · linarith only [h0, h11124, hlam]
                                            · rcases p11118_3 (m.d 1 2) (by simp) with h11126 | h11126
                                              · rcases p11118_3 (m.d 2 3) (by simp) with h11127 | h11127
                                                · linarith only [h11055, h11127, hlam]
                                                · rcases p11118_3 (m.d 2 4) (by simp) with h11129 | h11129
                                                  · linarith only [h11056, h11129, hlam]
                                                  · linarith only [h11129, h8379, hlam]
                                              · linarith only [h0, h11126, hlam]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h10991, h11055, h11058, h11061, h11065, h8378, hlam, p11118_2]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h10991, h11065, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h10991, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h8378, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11055, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11061, hlam, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11063, hlam, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11056, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11056, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            rcases p11118_3 (m.d 0 2) (by simp) with h11144 | h11144
                                            · linarith only [h11144, h8379, hlam]
                                            · linarith only [h11144, h8378, hlam]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h10991, h11055, h11058, h11061, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11057, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11057, hlam, p11118_0]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            rcases p11118_3 (m.d 0 2) (by simp) with h11151 | h11151
                                            · linarith only [h10991, h11151, hlam]
                                            · linarith only [h11151, h8378, hlam]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [h11065, hlam, p11118_1]
                                          · have p11118_0 := h11118c.1
                                            have p11118_1 := h11118c.2.1
                                            have p11118_2 := h11118c.2.2.1
                                            have p11118_3 := h11118c.2.2.2
                                            linarith only [hlam, p11118_0]
                                        · linarith only [h11117, hlam, p11067_0]
                                      · linarith only [h11116, h7647, hlam]
                                    · linarith only [h11115, h6794, hlam]
                                  · linarith only [h0, h11114, hlam]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h11057, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h11059, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [h11060, hlam, p11067_0]
                              · have p11067_0 := h11067c.1
                                have p11067_1 := h11067c.2.1
                                have p11067_2 := h11067c.2.2.1
                                have p11067_3 := h11067c.2.2.2
                                linarith only [hlam, p11067_0]
                            · linarith only [h11054, h11061, h11066, h8378, h8379, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11054, h11065, h8379, hlam]
                    · linarith only [h11054, h11060, h7647, h8379, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h11052, h11054, h11058, h11059, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11168 | h11168
                  · linarith only [h10991, h11057, h11058, h11168, h8378, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11170 | h11170
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11171 | h11171
                      · linarith only [h11056, h11058, h11171, h8378, h8379, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11173 | h11173
                        · linarith only [h10991, h11057, h11168, h11173, h8378, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11175 | h11175
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11176 | h11176
                            · rcases h1bigk with h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c | h11177c
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h0, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h6794, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h7647, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h8170, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                rcases p11177_3 (m.d 0 1) (by simp) with h11183 | h11183
                                · linarith only [h11183, hlam, p11177_0]
                                · rcases p11177_3 (m.d 1 2) (by simp) with h11185 | h11185
                                  · rcases p11177_3 (m.d 1 3) (by simp) with h11186 | h11186
                                    · linarith only [h11055, h11186, hlam]
                                    · linarith only [h11186, h6794, hlam]
                                  · linarith only [h11185, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h6794, hc01, hc12, hlam, hphi, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h10991, h11057, h11170, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h10991, h11057, h8378, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11058, hc01, hc34, hlam, hphi, ht12, ht23, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11055, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11058, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11168, hlam, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                rcases p11177_3 (m.d 0 1) (by simp) with h11199 | h11199
                                · linarith only [h11199, hlam, p11177_0]
                                · rcases p11177_3 (m.d 1 2) (by simp) with h11201 | h11201
                                  · rcases p11177_3 (m.d 1 3) (by simp) with h11202 | h11202
                                    · linarith only [h11058, h11202, hlam]
                                    · linarith only [h11202, h6794, hlam]
                                  · linarith only [h0, h11201, hlam]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11056, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h6794, hc01, hc14, hlam, hphi, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h10991, h11057, h11058, h8378, hc23, hc34, hlam, hphi, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                rcases p11177_3 (m.d 0 1) (by simp) with h11210 | h11210
                                · linarith only [h11210, hlam, p11177_0]
                                · rcases p11177_3 (m.d 1 2) (by simp) with h11212 | h11212
                                  · rcases p11177_3 (m.d 1 3) (by simp) with h11213 | h11213
                                    · linarith only [h11168, h11213, hlam]
                                    · linarith only [h11213, h6794, hlam]
                                  · linarith only [h0, h11212, hlam]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11057, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h6794, hc01, hc15, hlam, hphi, p11177_1]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [h11170, hlam, p11177_0]
                              · have p11177_0 := h11177c.1
                                have p11177_1 := h11177c.2.1
                                have p11177_2 := h11177c.2.2.1
                                have p11177_3 := h11177c.2.2.2
                                linarith only [hlam, p11177_0]
                            · linarith only [h11054, h11058, h11176, h7647, hlam]
                          · linarith only [h11054, h11175, h8379, hlam]
                    · linarith only [h11054, h11056, h11170, h8379, hlam]
              · linarith only [h11054, h11056, h11057, h8379, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11225 | h11225
              · linarith only [h10991, h11056, h11225, h8378, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11227 | h11227
                · linarith only [h11052, h11054, h11055, h11056, h11227, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11229 | h11229
                  · linarith only [h11055, h11225, h11229, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11231 | h11231
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11232 | h11232
                      · linarith only [h11052, h11232, h8378, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11234 | h11234
                        · linarith only [h0, h11056, h11229, h11232, h11234, h8378, hc13, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11236 | h11236
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11237 | h11237
                            · rcases h1bigk with h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c | h11238c
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h0, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h6794, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h7647, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h8170, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11225, h11232, h11236, hc01, hc34, hlam, hphi, ht12, ht23, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11225, h11232, h11236, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11056, hlam, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11225, hlam, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11055, h11225, h11232, h11236, hc01, hc34, hlam, hphi, ht12, ht23, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11055, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11227, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11229, hlam, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                rcases p11238_3 (m.d 0 1) (by simp) with h11254 | h11254
                                · linarith only [h11254, hlam, p11238_0]
                                · rcases p11238_3 (m.d 1 2) (by simp) with h11256 | h11256
                                  · linarith only [h11056, h11256, hlam]
                                  · linarith only [h0, h11256, hlam]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11056, h11232, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11055, h11056, h11225, h11232, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                rcases p11238_3 (m.d 0 1) (by simp) with h11263 | h11263
                                · linarith only [h11263, hlam, p11238_0]
                                · rcases p11238_3 (m.d 1 2) (by simp) with h11265 | h11265
                                  · linarith only [h11225, h11265, hlam]
                                  · linarith only [h0, h11265, hlam]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11055, h6794, hc01, hc15, hlam, hphi, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11225, h11232, h11236, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p11238_1]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [h11231, hlam, p11238_0]
                              · have p11238_0 := h11238c.1
                                have p11238_1 := h11238c.2.1
                                have p11238_2 := h11238c.2.2.1
                                have p11238_3 := h11238c.2.2.2
                                linarith only [hlam, p11238_0]
                            · linarith only [h11232, h11237, h8378, h8379, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h11054, h11055, h11056, h11236, h6794, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h11054, h11231, h7647, hlam]
          · linarith only [h0, h11055, h8378, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11276 | h11276
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11277 | h11277
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11278 | h11278
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11279 | h11279
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11280 | h11280
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11281 | h11281
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11282 | h11282
                      · linarith only [h11052, h11054, h11276, h11279, h11281, h11282, h6794, h8378, h8379, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11284 | h11284
                        · linarith only [h11054, h11276, h11279, h11281, h11284, h8378, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11286 | h11286
                          · linarith only [h11054, h11276, h11279, h11282, h11286, h8378, h8379, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11286, h8378, h8379, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h11277, h11281, h8378, h8379, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h11052, h11279, h11280, h6794, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11291 | h11291
                  · linarith only [h10991, h11278, h11279, h11291, h8378, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11293 | h11293
                    · linarith only [h11054, h11279, h11293, h8378, h8379, hc23, hc34, hlam, hphi]
                    · linarith only [h11277, h11293, h8378, h8379, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h11277, h11278, h8378, h8379, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11297 | h11297
              · linarith only [h10991, h11277, h11297, h8378, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11299 | h11299
                · linarith only [h11052, h11276, h11277, h11299, h6794, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11301 | h11301
                  · linarith only [h11276, h11297, h11301, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11303 | h11303
                    · linarith only [h11054, h11299, h11303, h8378, h8379, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11305 | h11305
                      · linarith only [h0, h11277, h11303, h11305, h8378, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11307 | h11307
                        · linarith only [h0, h11277, h11303, h11307, h8378, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11309 | h11309
                          · linarith only [h0, h11277, h11303, h11305, h11309, h8378, hc23, hc34, hlam, hphi]
                          · linarith only [h11309, h8378, h8379, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h11276, h8378, h8379, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 8096000 in
set_option maxHeartbeats 8096000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s11 m hb1 hb2 hb4 hb5 h0 h6794 h7647 h8170 h8378

set_option maxHeartbeats 8096000 in
set_option maxHeartbeats 8096000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8378 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h11313 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  rcases m.htr 0 2 5 (by decide) (by decide) with h11314 | h11314
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11315 | h11315
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11316 | h11316
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11317 | h11317
        · linarith only [h11314, h11317, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11319 | h11319
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11320 | h11320
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11321 | h11321
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11322 | h11322
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11323 | h11323
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11324 | h11324
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11325 | h11325
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11326 | h11326
                        · linarith only [h11313, h11326, h8378, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11328 | h11328
                          · linarith only [h11324, h11326, h11328, hlam]
                          · rcases h1bigk with h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h0, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h6794, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h7647, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h8170, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, hc01, hc23, hlam, hphi, ht12, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, hlam, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11316, h11317, h11324, h11326, h7647, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, h8170, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11330_1, u5ehi0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              rcases p11330_3 (m.d 0 1) (by simp) with h11341 | h11341
                              · linarith only [h11341, hlam, p11330_0]
                              · rcases p11330_3 (m.d 1 2) (by simp) with h11343 | h11343
                                · linarith only [h11317, h11343, hlam]
                                · linarith only [h0, h11343, hlam]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11316, h11317, h11324, h11326, h7647, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, h8170, hc01, hc23, hlam, hphi, ht12, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, h11319, hc01, hc23, hlam, hphi, ht12, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11319, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11321, hlam, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, h11319, h8170, hc01, hc23, hlam, hphi, ht12, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11317, h11320, hc01, hc23, hlam, hphi, ht12, p11330_1]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11320, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11322, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [h11323, hlam, p11330_0]
                            · have p11330_0 := h11330c.1
                              have p11330_1 := h11330c.2.1
                              have p11330_2 := h11330c.2.2.1
                              have p11330_3 := h11330c.2.2.2
                              linarith only [hlam, p11330_0]
                      · linarith only [h0, h11317, h11325, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11313, h11316, h11317, h11324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h11316, h11323, h7647, hlam]
                · linarith only [h11317, h11320, h11322, hlam]
              · linarith only [h11315, h11321, h6794, hlam]
            · linarith only [h0, h11314, h11320, hlam]
          · linarith only [h0, h11313, h11319, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11367 | h11367
        · linarith only [h11314, h11367, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11369 | h11369
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11370 | h11370
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11371 | h11371
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11372 | h11372
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11373 | h11373
                  · linarith only [h11316, h11367, h11369, h11373, h7647, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11375 | h11375
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11376 | h11376
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11377 | h11377
                        · linarith only [h0, h11313, h11367, h11377, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11379 | h11379
                          · linarith only [h0, h11314, h11367, h11373, h11375, h11377, h11379, h7647, hc01, hc23, hlam, hphi, ht12]
                          · rcases h1bigk with h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h0, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h6794, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h7647, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h8170, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, hc01, hc23, hlam, hphi, ht12, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, hlam, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, h7647, hc01, hc23, hlam, hphi, ht12, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, h11373, h7647, hc01, hc23, hlam, hphi, ht12, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              rcases p11381_3 (m.d 0 1) (by simp) with h11392 | h11392
                              · linarith only [h11392, hlam, p11381_0]
                              · rcases p11381_3 (m.d 1 2) (by simp) with h11394 | h11394
                                · linarith only [h11367, h11394, hlam]
                                · linarith only [h0, h11394, hlam]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h0, h11314, hc13, hlam, hphi, ht01, ht0b, ht5b, p11381_1, u5ehi2]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h7647, hc01, hc13, hlam, hphi, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, h11373, h7647, hc01, hc23, hlam, hphi, ht12, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11373, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11369, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11371, hlam, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11373, hlam, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, h11370, hc01, hc23, hlam, hphi, ht12, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11370, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11372, hlam, p11381_0]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [h11367, h11370, h7647, hc01, hc23, hlam, hphi, ht12, p11381_1]
                            · have p11381_0 := h11381c.1
                              have p11381_1 := h11381c.2.1
                              have p11381_2 := h11381c.2.2.1
                              have p11381_3 := h11381c.2.2.2
                              linarith only [hlam, p11381_0]
                      · linarith only [h0, h11367, h11376, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11314, h11367, h11375, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h11367, h11370, h11372, hlam]
              · linarith only [h0, h11313, h11315, h11367, h11371, hlam]
            · linarith only [h0, h11314, h11370, hlam]
          · linarith only [h0, h11313, h11369, hlam]
    · linarith only [h11313, h11315, h8378, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11418 | h11418
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11419 | h11419
      · linarith only [h11313, h11314, h11419, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11421 | h11421
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11422 | h11422
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11423 | h11423
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11424 | h11424
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11425 | h11425
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11426 | h11426
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11427 | h11427
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11428 | h11428
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11429 | h11429
                        · linarith only [h11313, h11314, h11419, h11423, h11429, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11431 | h11431
                          · linarith only [h11313, h11314, h11427, h11429, h11431, hlam]
                          · rcases h1bigk with h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c | h11433c
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h0, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h6794, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h7647, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h8170, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              rcases p11433_3 (m.d 0 1) (by simp) with h11439 | h11439
                              · linarith only [h11439, hlam, p11433_0]
                              · rcases p11433_3 (m.d 1 2) (by simp) with h11441 | h11441
                                · rcases p11433_3 (m.d 1 3) (by simp) with h11442 | h11442
                                  · linarith only [h11421, h11442, hlam]
                                  · linarith only [h11442, h6794, hlam]
                                · linarith only [h11441, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11314, h11424, h11426, h11429, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11313, h11314, h11426, h11427, h11429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h8170, hc01, hc12, hlam, hphi, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              rcases p11433_3 (m.d 0 1) (by simp) with h11450 | h11450
                              · linarith only [h11450, hlam, p11433_0]
                              · rcases p11433_3 (m.d 1 2) (by simp) with h11452 | h11452
                                · rcases p11433_3 (m.d 1 3) (by simp) with h11453 | h11453
                                  · rcases p11433_3 (m.d 1 4) (by simp) with h11454 | h11454
                                    · linarith only [h11424, h11454, hlam]
                                    · linarith only [h11454, h7647, hlam]
                                  · linarith only [h11453, hlam, p11433_0]
                                · linarith only [h0, h11452, hlam]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11421, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11313, h11314, h11426, h11427, h11429, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11313, h11314, h11421, h11426, h11427, h11429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              rcases p11433_3 (m.d 0 1) (by simp) with h11463 | h11463
                              · linarith only [h11463, hlam, p11433_0]
                              · rcases p11433_3 (m.d 1 2) (by simp) with h11465 | h11465
                                · rcases p11433_3 (m.d 1 3) (by simp) with h11466 | h11466
                                  · rcases p11433_3 (m.d 1 4) (by simp) with h11467 | h11467
                                    · rcases p11433_3 (m.d 1 5) (by simp) with h11468 | h11468
                                      · linarith only [h11426, h11468, hlam]
                                      · linarith only [h11468, h8170, hlam]
                                    · linarith only [h11467, hlam, p11433_0]
                                  · linarith only [h11466, h6794, hlam]
                                · linarith only [h0, h11465, hlam]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11422, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11424, hlam, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11313, h11314, h11426, h11427, h11429, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11433_1]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              rcases p11433_3 (m.d 0 1) (by simp) with h11478 | h11478
                              · linarith only [h11478, hlam, p11433_0]
                              · rcases p11433_3 (m.d 1 2) (by simp) with h11480 | h11480
                                · rcases p11433_3 (m.d 1 3) (by simp) with h11481 | h11481
                                  · rcases p11433_3 (m.d 1 4) (by simp) with h11482 | h11482
                                    · rcases p11433_3 (m.d 1 5) (by simp) with h11483 | h11483
                                      · rcases h2bigk with h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c | h11484c
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h0, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h8378, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11314, h11427, h11429, hc34, hc45, hlam, hphi, p11484_1]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11314, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          rcases p11484_3 (m.d 0 2) (by simp) with h11490 | h11490
                                          · linarith only [h0, h11490, hlam]
                                          · rcases p11484_3 (m.d 1 2) (by simp) with h11492 | h11492
                                            · rcases p11484_3 (m.d 2 3) (by simp) with h11493 | h11493
                                              · linarith only [h11421, h11493, hlam]
                                              · linarith only [h11493, h8378, hlam]
                                            · linarith only [h0, h11492, hlam]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11428, hc12, hlam, hphi, ht01, ht0b, ht5b, p11484_1, u5ehi3]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11313, h11314, h11421, h11424, h11426, h11429, hlam, p11484_2]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11313, h11314, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11484_1]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11313, h11421, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11484_1]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11421, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          rcases p11484_3 (m.d 0 2) (by simp) with h11504 | h11504
                                          · linarith only [h11504, h8378, hlam]
                                          · linarith only [h11313, h11504, hlam]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11313, h11314, h11421, h11427, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11484_1]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11313, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11422, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11427, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11429, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11313, h11423, h11427, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11484_1]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11423, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [h11428, hlam, p11484_0]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          rcases p11484_3 (m.d 0 2) (by simp) with h11516 | h11516
                                          · linarith only [h11314, h11516, hlam]
                                          · linarith only [h11313, h11516, hlam]
                                        · have p11484_0 := h11484c.1
                                          have p11484_1 := h11484c.2.1
                                          have p11484_2 := h11484c.2.2.1
                                          have p11484_3 := h11484c.2.2.2
                                          linarith only [hlam, p11484_0]
                                      · linarith only [h11483, hlam, p11433_0]
                                    · linarith only [h11482, h7647, hlam]
                                  · linarith only [h11481, h6794, hlam]
                                · linarith only [h0, h11480, hlam]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11423, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11425, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [h11426, hlam, p11433_0]
                            · have p11433_0 := h11433c.1
                              have p11433_1 := h11433c.2.1
                              have p11433_2 := h11433c.2.2.1
                              have p11433_3 := h11433c.2.2.2
                              linarith only [hlam, p11433_0]
                      · linarith only [h11313, h11421, h11425, h11427, h11428, h8378, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11418, h11427, h8378, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11530 | h11530
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11531 | h11531
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11532 | h11532
                        · linarith only [h11313, h11314, h11426, h11531, h11532, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11534 | h11534
                          · linarith only [h11313, h11314, h11426, h11530, h11531, h11534, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                          · rcases h1bigk with h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c | h11536c
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h0, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h6794, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h7647, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h8170, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              rcases p11536_3 (m.d 0 1) (by simp) with h11542 | h11542
                              · linarith only [h11542, hlam, p11536_0]
                              · rcases p11536_3 (m.d 1 2) (by simp) with h11544 | h11544
                                · rcases p11536_3 (m.d 1 3) (by simp) with h11545 | h11545
                                  · linarith only [h11421, h11545, hlam]
                                  · linarith only [h11545, h6794, hlam]
                                · linarith only [h11544, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h6794, hc01, hc12, hlam, hphi, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h7647, hc01, hc12, hlam, hphi, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11313, h11314, h11423, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              rcases p11536_3 (m.d 0 1) (by simp) with h11553 | h11553
                              · linarith only [h11553, hlam, p11536_0]
                              · rcases p11536_3 (m.d 1 2) (by simp) with h11555 | h11555
                                · rcases p11536_3 (m.d 1 3) (by simp) with h11556 | h11556
                                  · rcases p11536_3 (m.d 1 4) (by simp) with h11557 | h11557
                                    · linarith only [h11424, h11557, hlam]
                                    · linarith only [h11557, h7647, hlam]
                                  · linarith only [h11556, hlam, p11536_0]
                                · linarith only [h0, h11555, hlam]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11421, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h7647, hc01, hc13, hlam, hphi, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11313, h11314, h11421, h11423, h11530, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11426, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11422, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11424, hlam, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11426, hlam, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              rcases p11536_3 (m.d 0 1) (by simp) with h11571 | h11571
                              · linarith only [h11571, hlam, p11536_0]
                              · rcases p11536_3 (m.d 1 2) (by simp) with h11573 | h11573
                                · rcases p11536_3 (m.d 1 3) (by simp) with h11574 | h11574
                                  · rcases p11536_3 (m.d 1 4) (by simp) with h11575 | h11575
                                    · linarith only [h11426, h11575, hlam]
                                    · linarith only [h11575, h7647, hlam]
                                  · linarith only [h11574, h6794, hlam]
                                · linarith only [h0, h11573, hlam]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11423, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h11425, hlam, p11536_0]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [h7647, hc01, hc15, hlam, hphi, p11536_1]
                            · have p11536_0 := h11536c.1
                              have p11536_1 := h11536c.2.1
                              have p11536_2 := h11536c.2.2.1
                              have p11536_3 := h11536c.2.2.2
                              linarith only [hlam, p11536_0]
                      · linarith only [h11313, h11421, h11425, h11530, h11531, h8378, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11418, h11530, h8378, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11586 | h11586
                  · linarith only [h11419, h11424, h11425, h11586, h7647, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11588 | h11588
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11589 | h11589
                      · linarith only [h11425, h11589, h6794, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11591 | h11591
                        · linarith only [h11313, h11421, h11586, h11591, h8378, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11593 | h11593
                          · linarith only [h11313, h11421, h11425, h11586, h11588, h11593, h8378, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h11313, h11421, h11425, h11593, h8378, hc24, hc45, hlam, hphi]
                    · linarith only [h11418, h11588, h8378, hlam]
              · linarith only [h11313, h11418, h11421, h11424, h8378, hlam]
            · linarith only [h11313, h11421, h11423, h8378, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h11313, h11421, h11422, h8378, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11600 | h11600
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11601 | h11601
            · linarith only [h11313, h11314, h11421, h11601, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11603 | h11603
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11604 | h11604
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11605 | h11605
                  · linarith only [h11419, h11421, h11600, h11605, h7647, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11607 | h11607
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11608 | h11608
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11609 | h11609
                        · linarith only [h0, h11313, h11601, h11605, h11608, h11609, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11611 | h11611
                          · linarith only [h0, h11601, h11609, h11611, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h1bigk with h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c | h11613c
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h0, hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h6794, hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h7647, hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h8170, hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11601, hc01, hc25, hlam, hphi, ht12, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11421, hlam, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11601, h11609, hc14, hc45, hlam, hphi, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11601, hlam, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              rcases p11613_3 (m.d 0 1) (by simp) with h11624 | h11624
                              · linarith only [h11624, hlam, p11613_0]
                              · rcases p11613_3 (m.d 1 2) (by simp) with h11626 | h11626
                                · linarith only [h11421, h11626, hlam]
                                · linarith only [h0, h11626, hlam]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h0, h11421, hc01, hc23, hlam, hphi, ht12, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11421, h7647, hc01, hc23, hlam, hphi, ht12, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11421, h11600, h11601, h7647, hc01, hc23, hlam, hphi, ht12, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11600, h11601, hc01, hc25, hlam, hphi, ht12, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11600, hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11603, hlam, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11605, hlam, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              rcases p11613_3 (m.d 0 1) (by simp) with h11638 | h11638
                              · linarith only [h11638, hlam, p11613_0]
                              · rcases p11613_3 (m.d 1 2) (by simp) with h11640 | h11640
                                · linarith only [h11601, h11640, hlam]
                                · linarith only [h0, h11640, hlam]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h11604, hlam, p11613_0]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [h7647, hc01, hc15, hlam, hphi, p11613_1]
                            · have p11613_0 := h11613c.1
                              have p11613_1 := h11613c.2.1
                              have p11613_2 := h11613c.2.2.1
                              have p11613_3 := h11613c.2.2.2
                              linarith only [hlam, p11613_0]
                      · linarith only [h11421, h11604, h11608, hlam]
                    · linarith only [h11418, h11421, h11607, h6794, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11649 | h11649
                  · linarith only [h11419, h11421, h11600, h11604, h11649, h7647, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11651 | h11651
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11652 | h11652
                      · linarith only [h0, h11421, h11604, h11652, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h11421, h11600, h11652, h7647, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h11421, h11600, h11651, h7647, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h11418, h11421, h11600, h11603, h7647, hlam]
          · linarith only [h0, h11313, h11600, hlam]
    · linarith only [h11313, h11418, h8378, hlam]

end R2N4
