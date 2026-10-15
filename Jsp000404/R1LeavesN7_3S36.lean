import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13248000 in
set_option maxHeartbeats 13248000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s15_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h17994 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h17995 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h17996 | h17996
  · rcases m.htr 0 2 5 (by decide) (by decide) with h17997 | h17997
    · rcases m.htr 0 3 4 (by decide) (by decide) with h17998 | h17998
      · rcases m.htr 0 3 5 (by decide) (by decide) with h17999 | h17999
        · rcases m.htr 0 4 5 (by decide) (by decide) with h18000 | h18000
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18001 | h18001
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18002 | h18002
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18003 | h18003
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18004 | h18004
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18005 | h18005
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18006 | h18006
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18007 | h18007
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18008 | h18008
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18009 | h18009
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18010 | h18010
                              · rcases h1bigk with h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h0, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h14799, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h16563, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18016 | h18016
                                  · rcases p18011_3 (m.d 1 2) (by simp) with h18017 | h18017
                                    · rcases p18011_3 (m.d 1 3) (by simp) with h18018 | h18018
                                      · rcases p18011_3 (m.d 1 4) (by simp) with h18019 | h18019
                                        · rcases p18011_3 (m.d 1 5) (by simp) with h18020 | h18020
                                          · linarith only [h18020, hlam, p18011_0]
                                          · rcases h3bigk with h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c | h18022c
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h14799, hlam, p18022_1]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h14799, h18001, h18007, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18022_1]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              rcases p18022_3 (m.d 0 3) (by simp) with h18026 | h18026
                                              · rcases p18022_3 (m.d 1 3) (by simp) with h18027 | h18027
                                                · rcases p18022_3 (m.d 2 3) (by simp) with h18028 | h18028
                                                  · linarith only [h17995, h18028, hlam]
                                                  · linarith only [h18007, h18028, hlam]
                                                · linarith only [h18004, h18027, hlam]
                                              · linarith only [h18026, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              rcases p18022_3 (m.d 0 3) (by simp) with h18033 | h18033
                                              · rcases p18022_3 (m.d 1 3) (by simp) with h18034 | h18034
                                                · rcases p18022_3 (m.d 2 3) (by simp) with h18035 | h18035
                                                  · linarith only [h17995, h18035, hlam]
                                                  · linarith only [h18008, h18035, hlam]
                                                · linarith only [h18005, h18034, hlam]
                                              · linarith only [h18033, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h14799, h18001, h18003, h18008, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18011_1, p18022_1]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18001, h18007, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18022_1]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              rcases p18022_3 (m.d 0 3) (by simp) with h18043 | h18043
                                              · linarith only [h14799, h18043, hlam]
                                              · linarith only [h17998, h18043, hlam]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h14799, h18003, h18008, hlam, p18011_1, p18022_2]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h17995, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18001, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h17995, h18010, hc02, hc45, hlam, hphi, ht0b, ht5b, p18022_1]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              rcases p18022_3 (m.d 0 3) (by simp) with h18051 | h18051
                                              · rcases p18022_3 (m.d 1 3) (by simp) with h18052 | h18052
                                                · rcases p18022_3 (m.d 2 3) (by simp) with h18053 | h18053
                                                  · rcases p18022_3 (m.d 3 4) (by simp) with h18054 | h18054
                                                    · linarith only [h18007, h18054, hlam]
                                                    · linarith only [h18010, h18054, hlam]
                                                  · linarith only [h18053, hlam, p18022_0]
                                                · linarith only [h18005, h18052, hlam]
                                              · linarith only [h17999, h18051, hlam]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h17998, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18004, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18007, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h0, h17995, h18007, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18022_1]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h17999, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18005, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18008, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [h18010, hlam, p18022_0]
                                            · have p18022_0 := h18022c.1
                                              have p18022_1 := h18022c.2.1
                                              have p18022_2 := h18022c.2.2.1
                                              have p18022_3 := h18022c.2.2.2
                                              linarith only [hlam, p18022_0]
                                        · linarith only [h18006, h18019, hlam]
                                      · linarith only [h18005, h18018, hlam]
                                    · linarith only [h18003, h18017, hlam]
                                  · linarith only [h18016, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18074 | h18074
                                  · linarith only [h18074, hlam, p18011_0]
                                  · rcases p18011_3 (m.d 1 2) (by simp) with h18076 | h18076
                                    · rcases p18011_3 (m.d 1 3) (by simp) with h18077 | h18077
                                      · linarith only [h18001, h18077, hlam]
                                      · linarith only [h14799, h18077, hlam]
                                    · linarith only [h18076, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18011_1]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h16563, h17994, h18003, h18008, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18011_1]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18084 | h18084
                                  · linarith only [h0, h18084, hlam]
                                  · linarith only [h17994, h18084, hlam]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18087 | h18087
                                  · linarith only [h18087, hlam, p18011_0]
                                  · rcases p18011_3 (m.d 1 2) (by simp) with h18089 | h18089
                                    · rcases p18011_3 (m.d 1 3) (by simp) with h18090 | h18090
                                      · rcases p18011_3 (m.d 1 4) (by simp) with h18091 | h18091
                                        · linarith only [h18004, h18091, hlam]
                                        · linarith only [h16563, h18091, hlam]
                                      · linarith only [h18090, hlam, p18011_0]
                                    · linarith only [h0, h18089, hlam]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h18001, hlam, p18011_1]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h16563, h17994, h18001, h18003, h18008, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18011_1]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18099 | h18099
                                  · linarith only [h14799, h18099, hlam]
                                  · linarith only [h17994, h18099, hlam]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18102 | h18102
                                  · linarith only [h18102, hlam, p18011_0]
                                  · rcases p18011_3 (m.d 1 2) (by simp) with h18104 | h18104
                                    · rcases p18011_3 (m.d 1 3) (by simp) with h18105 | h18105
                                      · rcases p18011_3 (m.d 1 4) (by simp) with h18106 | h18106
                                        · rcases p18011_3 (m.d 1 5) (by simp) with h18107 | h18107
                                          · linarith only [h18006, h18107, hlam]
                                          · rcases h3bigk with h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c | h18109c
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h14799, hlam, p18109_1]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18007, h18010, hc03, hc45, hlam, hphi, ht0b, ht5b, p18109_1]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              rcases p18109_3 (m.d 0 3) (by simp) with h18113 | h18113
                                              · rcases p18109_3 (m.d 1 3) (by simp) with h18114 | h18114
                                                · rcases p18109_3 (m.d 2 3) (by simp) with h18115 | h18115
                                                  · linarith only [h17995, h18115, hlam]
                                                  · linarith only [h18007, h18115, hlam]
                                                · linarith only [h18004, h18114, hlam]
                                              · linarith only [h18113, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              rcases p18109_3 (m.d 0 3) (by simp) with h18120 | h18120
                                              · rcases p18109_3 (m.d 1 3) (by simp) with h18121 | h18121
                                                · rcases p18109_3 (m.d 2 3) (by simp) with h18122 | h18122
                                                  · linarith only [h17995, h18122, hlam]
                                                  · linarith only [h18008, h18122, hlam]
                                                · linarith only [h18005, h18121, hlam]
                                              · linarith only [h18120, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h17995, h18001, h18007, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18109_1]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18001, h18007, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18109_1]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              rcases p18109_3 (m.d 0 3) (by simp) with h18130 | h18130
                                              · linarith only [h14799, h18130, hlam]
                                              · linarith only [h17998, h18130, hlam]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h17994, h18003, h18004, h18008, hlam, p18011_1, p18109_2]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h17995, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18001, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h0, h17995, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18109_1]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              rcases p18109_3 (m.d 0 3) (by simp) with h18138 | h18138
                                              · rcases p18109_3 (m.d 1 3) (by simp) with h18139 | h18139
                                                · rcases p18109_3 (m.d 2 3) (by simp) with h18140 | h18140
                                                  · rcases p18109_3 (m.d 3 4) (by simp) with h18141 | h18141
                                                    · linarith only [h18007, h18141, hlam]
                                                    · linarith only [h18010, h18141, hlam]
                                                  · linarith only [h18140, hlam, p18109_0]
                                                · linarith only [h18005, h18139, hlam]
                                              · linarith only [h17999, h18138, hlam]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h17998, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18004, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18007, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h0, h17995, h18007, h18010, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18109_1]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h17999, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18005, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18008, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [h18010, hlam, p18109_0]
                                            · have p18109_0 := h18109c.1
                                              have p18109_1 := h18109c.2.1
                                              have p18109_2 := h18109c.2.2.1
                                              have p18109_3 := h18109c.2.2.2
                                              linarith only [hlam, p18109_0]
                                        · linarith only [h18106, hlam, p18011_0]
                                      · linarith only [h14799, h18105, hlam]
                                    · linarith only [h0, h18104, hlam]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h18002, hlam, p18011_1]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h18004, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  rcases p18011_3 (m.d 0 1) (by simp) with h18163 | h18163
                                  · linarith only [h16563, h18163, hlam]
                                  · linarith only [h17994, h18163, hlam]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h17994, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h18003, hlam, p18011_1]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h18005, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [h18006, hlam, p18011_0]
                                · have p18011_0 := h18011c.1
                                  have p18011_1 := h18011c.2.1
                                  have p18011_2 := h18011c.2.2.1
                                  have p18011_3 := h18011c.2.2.2
                                  linarith only [hlam, p18011_0]
                              · rcases h1bigk with h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c | h18171c
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h0, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h14799, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h16563, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h0, h18003, h18009, h18010, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h17994, h18003, h18009, h18010, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h16563, h17994, h18003, h18009, h18010, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  rcases p18171_3 (m.d 0 1) (by simp) with h18181 | h18181
                                  · linarith only [h0, h18181, hlam]
                                  · linarith only [h17994, h18181, hlam]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h17994, h18003, h18009, h18010, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h18001, hlam, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h16563, h17994, h18001, h18003, h18009, h18010, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  rcases p18171_3 (m.d 0 1) (by simp) with h18188 | h18188
                                  · linarith only [h14799, h18188, hlam]
                                  · linarith only [h17994, h18188, hlam]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h17994, h18003, h18009, h18010, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h18002, hlam, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h18004, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  rcases p18171_3 (m.d 0 1) (by simp) with h18195 | h18195
                                  · linarith only [h16563, h18195, hlam]
                                  · linarith only [h17994, h18195, hlam]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h17994, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h18003, hlam, p18171_1]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h18005, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [h18006, hlam, p18171_0]
                                · have p18171_0 := h18171c.1
                                  have p18171_1 := h18171c.2.1
                                  have p18171_2 := h18171c.2.2.1
                                  have p18171_3 := h18171c.2.2.2
                                  linarith only [hlam, p18171_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18203 | h18203
                              · linarith only [h18007, h18009, h18203, hlam]
                              · rcases h1bigk with h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c | h18205c
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h0, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h14799, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h16563, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h0, h18006, h18007, h18009, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h17994, h18006, h18007, h18009, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h16563, h17994, h18006, h18007, h18009, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  rcases p18205_3 (m.d 0 1) (by simp) with h18215 | h18215
                                  · linarith only [h0, h18215, hlam]
                                  · linarith only [h17994, h18215, hlam]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h17994, h18006, h18007, h18009, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h18001, hlam, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h16563, h17994, h18001, h18006, h18007, h18009, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  rcases p18205_3 (m.d 0 1) (by simp) with h18222 | h18222
                                  · linarith only [h14799, h18222, hlam]
                                  · linarith only [h17994, h18222, hlam]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h17994, h18006, h18007, h18009, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h18002, hlam, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h18004, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  rcases p18205_3 (m.d 0 1) (by simp) with h18229 | h18229
                                  · linarith only [h16563, h18229, hlam]
                                  · linarith only [h17994, h18229, hlam]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h17994, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h18003, hlam, p18205_1]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h18005, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [h18006, hlam, p18205_0]
                                · have p18205_0 := h18205c.1
                                  have p18205_1 := h18205c.2.1
                                  have p18205_2 := h18205c.2.2.1
                                  have p18205_3 := h18205c.2.2.2
                                  linarith only [hlam, p18205_0]
                          · linarith only [h16563, h17994, h18001, h18004, h18005, h18007, h18008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18238 | h18238
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18239 | h18239
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18240 | h18240
                              · rcases h1bigk with h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c | h18241c
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h0, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h14799, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h16563, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18246 | h18246
                                  · rcases p18241_3 (m.d 1 2) (by simp) with h18247 | h18247
                                    · rcases p18241_3 (m.d 1 3) (by simp) with h18248 | h18248
                                      · rcases p18241_3 (m.d 1 4) (by simp) with h18249 | h18249
                                        · rcases p18241_3 (m.d 1 5) (by simp) with h18250 | h18250
                                          · linarith only [h18250, hlam, p18241_0]
                                          · rcases h3bigk with h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c | h18252c
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h14799, hlam, p18252_1]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              rcases p18252_3 (m.d 0 3) (by simp) with h18255 | h18255
                                              · rcases p18252_3 (m.d 1 3) (by simp) with h18256 | h18256
                                                · rcases p18252_3 (m.d 2 3) (by simp) with h18257 | h18257
                                                  · linarith only [h17995, h18257, hlam]
                                                  · rcases p18252_3 (m.d 3 4) (by simp) with h18259 | h18259
                                                    · linarith only [h17998, h18259, hlam]
                                                    · linarith only [h18007, h18259, hlam]
                                                · linarith only [h18001, h18256, hlam]
                                              · linarith only [h17995, h18255, hlam]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h14799, h18001, h18007, h18238, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18252_1]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h17998, h18007, h18238, hlam, p18252_2]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h14799, h18001, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p18241_1, p18252_1]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              rcases p18252_3 (m.d 0 3) (by simp) with h18268 | h18268
                                              · linarith only [h14799, h18268, hlam]
                                              · linarith only [h17995, h18268, hlam]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18001, h18007, h18238, h18240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18252_1]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h14799, h18003, h18238, hlam, p18241_1, p18252_2]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h17995, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18001, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18007, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h17998, h18007, h18240, hc03, hc45, hlam, hphi, ht0b, ht5b, p18252_1]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h17998, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18004, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h0, h17995, h17998, h18238, h18240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18252_1]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              rcases p18252_3 (m.d 0 3) (by simp) with h18282 | h18282
                                              · rcases p18252_3 (m.d 1 3) (by simp) with h18283 | h18283
                                                · rcases p18252_3 (m.d 2 3) (by simp) with h18284 | h18284
                                                  · linarith only [h18007, h18284, hlam]
                                                  · linarith only [h18238, h18284, hlam]
                                                · linarith only [h18005, h18283, hlam]
                                              · linarith only [h17999, h18282, hlam]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h17999, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18005, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18238, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [h18240, hlam, p18252_0]
                                            · have p18252_0 := h18252c.1
                                              have p18252_1 := h18252c.2.1
                                              have p18252_2 := h18252c.2.2.1
                                              have p18252_3 := h18252c.2.2.2
                                              linarith only [hlam, p18252_0]
                                        · linarith only [h18006, h18249, hlam]
                                      · linarith only [h18005, h18248, hlam]
                                    · linarith only [h18003, h18247, hlam]
                                  · linarith only [h18246, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18298 | h18298
                                  · linarith only [h18298, hlam, p18241_0]
                                  · rcases p18241_3 (m.d 1 2) (by simp) with h18300 | h18300
                                    · rcases p18241_3 (m.d 1 3) (by simp) with h18301 | h18301
                                      · linarith only [h18001, h18301, hlam]
                                      · linarith only [h14799, h18301, hlam]
                                    · linarith only [h18300, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18241_1]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h16563, h17994, h18003, h18238, h18240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18241_1]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18308 | h18308
                                  · linarith only [h0, h18308, hlam]
                                  · linarith only [h17994, h18308, hlam]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18311 | h18311
                                  · linarith only [h18311, hlam, p18241_0]
                                  · rcases p18241_3 (m.d 1 2) (by simp) with h18313 | h18313
                                    · rcases p18241_3 (m.d 1 3) (by simp) with h18314 | h18314
                                      · rcases p18241_3 (m.d 1 4) (by simp) with h18315 | h18315
                                        · linarith only [h18004, h18315, hlam]
                                        · linarith only [h16563, h18315, hlam]
                                      · linarith only [h18314, hlam, p18241_0]
                                    · linarith only [h0, h18313, hlam]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h18001, hlam, p18241_1]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h16563, h18001, hc01, hc12, hlam, hphi, p18241_1]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18323 | h18323
                                  · linarith only [h14799, h18323, hlam]
                                  · linarith only [h17994, h18323, hlam]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18326 | h18326
                                  · linarith only [h18326, hlam, p18241_0]
                                  · rcases p18241_3 (m.d 1 2) (by simp) with h18328 | h18328
                                    · rcases p18241_3 (m.d 1 3) (by simp) with h18329 | h18329
                                      · rcases p18241_3 (m.d 1 4) (by simp) with h18330 | h18330
                                        · rcases p18241_3 (m.d 1 5) (by simp) with h18331 | h18331
                                          · linarith only [h18006, h18331, hlam]
                                          · rcases h3bigk with h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c | h18333c
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h14799, hlam, p18333_1]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              rcases p18333_3 (m.d 0 3) (by simp) with h18336 | h18336
                                              · rcases p18333_3 (m.d 1 3) (by simp) with h18337 | h18337
                                                · rcases p18333_3 (m.d 2 3) (by simp) with h18338 | h18338
                                                  · linarith only [h17995, h18338, hlam]
                                                  · rcases p18333_3 (m.d 3 4) (by simp) with h18340 | h18340
                                                    · linarith only [h17998, h18340, hlam]
                                                    · linarith only [h18007, h18340, hlam]
                                                · linarith only [h18001, h18337, hlam]
                                              · linarith only [h17995, h18336, hlam]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18007, h18238, h18240, hc03, hc45, hlam, hphi, ht0b, ht5b, p18333_1]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h17998, h18007, h18238, hlam, p18333_2]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h17998, h18007, h18238, h18240, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18333_1]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              rcases p18333_3 (m.d 0 3) (by simp) with h18349 | h18349
                                              · linarith only [h14799, h18349, hlam]
                                              · linarith only [h17995, h18349, hlam]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18001, h18007, h18238, h18240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18333_1]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h14799, h17998, h18007, h18238, hlam, p18333_2]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h17995, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18001, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18007, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h17998, h18007, h18240, hc03, hc45, hlam, hphi, ht0b, ht5b, p18333_1]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h17998, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18004, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h0, h17995, h17998, h18238, h18240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18333_1]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              rcases p18333_3 (m.d 0 3) (by simp) with h18363 | h18363
                                              · rcases p18333_3 (m.d 1 3) (by simp) with h18364 | h18364
                                                · rcases p18333_3 (m.d 2 3) (by simp) with h18365 | h18365
                                                  · linarith only [h18007, h18365, hlam]
                                                  · linarith only [h18238, h18365, hlam]
                                                · linarith only [h18005, h18364, hlam]
                                              · linarith only [h17999, h18363, hlam]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h17999, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18005, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18238, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [h18240, hlam, p18333_0]
                                            · have p18333_0 := h18333c.1
                                              have p18333_1 := h18333c.2.1
                                              have p18333_2 := h18333c.2.2.1
                                              have p18333_3 := h18333c.2.2.2
                                              linarith only [hlam, p18333_0]
                                        · linarith only [h18330, hlam, p18241_0]
                                      · linarith only [h14799, h18329, hlam]
                                    · linarith only [h0, h18328, hlam]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h18002, hlam, p18241_1]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h18004, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  rcases p18241_3 (m.d 0 1) (by simp) with h18381 | h18381
                                  · linarith only [h16563, h18381, hlam]
                                  · linarith only [h17994, h18381, hlam]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h17994, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h18003, hlam, p18241_1]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h18005, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [h18006, hlam, p18241_0]
                                · have p18241_0 := h18241c.1
                                  have p18241_1 := h18241c.2.1
                                  have p18241_2 := h18241c.2.2.1
                                  have p18241_3 := h18241c.2.2.2
                                  linarith only [hlam, p18241_0]
                              · linarith only [h0, h17995, h17998, h18000, h18007, h18238, h18240, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h17994, h18006, h18007, h18238, h18239, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18391 | h18391
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18392 | h18392
                              · rcases h1bigk with h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c | h18393c
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h0, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h14799, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h16563, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h16563, h18001, h18004, h18005, h18238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h17994, h18005, h18238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h16563, h17994, h18005, h18238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  rcases p18393_3 (m.d 0 1) (by simp) with h18403 | h18403
                                  · linarith only [h0, h18403, hlam]
                                  · linarith only [h17994, h18403, hlam]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h17994, h18005, h18238, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h18001, hlam, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h16563, h17994, h18001, h18005, h18238, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  rcases p18393_3 (m.d 0 1) (by simp) with h18410 | h18410
                                  · linarith only [h14799, h18410, hlam]
                                  · linarith only [h17994, h18410, hlam]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h17994, h18005, h18238, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h18002, hlam, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h18004, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  rcases p18393_3 (m.d 0 1) (by simp) with h18417 | h18417
                                  · linarith only [h16563, h18417, hlam]
                                  · linarith only [h17994, h18417, hlam]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h17994, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h18003, hlam, p18393_1]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h18005, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [h18006, hlam, p18393_0]
                                · have p18393_0 := h18393c.1
                                  have p18393_1 := h18393c.2.1
                                  have p18393_2 := h18393c.2.2.1
                                  have p18393_3 := h18393c.2.2.2
                                  linarith only [hlam, p18393_0]
                              · linarith only [h0, h17996, h18007, h18391, h18392, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18426 | h18426
                              · rcases h1bigk with h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c | h18427c
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h0, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h14799, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h16563, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h0, h18005, h18007, h18391, h18426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h17994, h18005, h18007, h18391, h18426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h16563, h17994, h18005, h18007, h18391, h18426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  rcases p18427_3 (m.d 0 1) (by simp) with h18437 | h18437
                                  · linarith only [h0, h18437, hlam]
                                  · linarith only [h17994, h18437, hlam]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h17994, h18005, h18007, h18391, h18426, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h18001, hlam, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h16563, h17994, h18001, h18005, h18007, h18391, h18426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  rcases p18427_3 (m.d 0 1) (by simp) with h18444 | h18444
                                  · linarith only [h14799, h18444, hlam]
                                  · linarith only [h17994, h18444, hlam]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h17994, h18005, h18007, h18391, h18426, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h18002, hlam, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h18004, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  rcases p18427_3 (m.d 0 1) (by simp) with h18451 | h18451
                                  · linarith only [h16563, h18451, hlam]
                                  · linarith only [h17994, h18451, hlam]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h17994, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h18003, hlam, p18427_1]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h18005, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [h18006, hlam, p18427_0]
                                · have p18427_0 := h18427c.1
                                  have p18427_1 := h18427c.2.1
                                  have p18427_2 := h18427c.2.2.1
                                  have p18427_3 := h18427c.2.2.2
                                  linarith only [hlam, p18427_0]
                              · linarith only [h0, h17994, h18006, h18007, h18426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h16563, h17995, h17998, h18000, h18006, hc01, hc12, hlam, hphi]
                    · linarith only [h14799, h17999, h18005, hlam]
                  · linarith only [h14799, h17998, h18004, hlam]
                · linarith only [h0, h17997, h18003, hlam]
              · linarith only [h0, h17996, h18002, hlam]
            · linarith only [h0, h17995, h18001, hlam]
          · linarith only [h16563, h17994, h18000, hlam]
        · linarith only [h14799, h17994, h17999, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18468 | h18468
        · rcases m.htr 0 4 5 (by decide) (by decide) with h18469 | h18469
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18470 | h18470
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18471 | h18471
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18472 | h18472
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18473 | h18473
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18474 | h18474
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18475 | h18475
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18476 | h18476
                        · linarith only [h17995, h17998, h18476, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18478 | h18478
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18479 | h18479
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18480 | h18480
                              · rcases h1bigk with h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c | h18481c
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h0, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h16563, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, h17998, h18470, h18472, h18473, h18478, h18480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  rcases p18481_3 (m.d 0 1) (by simp) with h18487 | h18487
                                  · linarith only [h18487, hlam, p18481_0]
                                  · rcases p18481_3 (m.d 1 2) (by simp) with h18489 | h18489
                                    · rcases p18481_3 (m.d 1 3) (by simp) with h18490 | h18490
                                      · linarith only [h18470, h18490, hlam]
                                      · linarith only [h14799, h18490, hlam]
                                    · linarith only [h18489, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, h17998, h18473, hc01, hc12, hlam, hphi, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, h17994, h17998, h18472, h18473, h18478, h18480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, h17994, h17998, h18470, h18473, hlam, p18481_2]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  rcases p18481_3 (m.d 0 1) (by simp) with h18498 | h18498
                                  · linarith only [h18498, hlam, p18481_0]
                                  · rcases p18481_3 (m.d 1 2) (by simp) with h18500 | h18500
                                    · rcases p18481_3 (m.d 1 3) (by simp) with h18501 | h18501
                                      · rcases p18481_3 (m.d 1 4) (by simp) with h18502 | h18502
                                        · linarith only [h18473, h18502, hlam]
                                        · linarith only [h16563, h18502, hlam]
                                      · linarith only [h18501, hlam, p18481_0]
                                    · linarith only [h0, h18500, hlam]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h18470, hlam, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, h17994, h17998, h18470, h18472, h18473, h18478, h18480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h14799, h17994, h17998, h18473, hlam, p18481_2]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  rcases p18481_3 (m.d 0 1) (by simp) with h18511 | h18511
                                  · linarith only [h18511, hlam, p18481_0]
                                  · rcases p18481_3 (m.d 1 2) (by simp) with h18513 | h18513
                                    · rcases p18481_3 (m.d 1 3) (by simp) with h18514 | h18514
                                      · rcases p18481_3 (m.d 1 4) (by simp) with h18515 | h18515
                                        · rcases p18481_3 (m.d 1 5) (by simp) with h18516 | h18516
                                          · linarith only [h18475, h18516, hlam]
                                          · rcases h3bigk with h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c | h18518c
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h14799, hlam, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h17998, h18473, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h17998, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h17998, h18473, h18480, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              rcases p18518_3 (m.d 0 3) (by simp) with h18524 | h18524
                                              · linarith only [h14799, h18524, hlam]
                                              · rcases p18518_3 (m.d 1 3) (by simp) with h18526 | h18526
                                                · rcases p18518_3 (m.d 2 3) (by simp) with h18527 | h18527
                                                  · linarith only [h18470, h18527, hlam]
                                                  · rcases p18518_3 (m.d 3 4) (by simp) with h18529 | h18529
                                                    · linarith only [h18473, h18529, hlam]
                                                    · linarith only [h17998, h18529, hlam]
                                                · linarith only [h14799, h18526, hlam]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              rcases p18518_3 (m.d 0 3) (by simp) with h18534 | h18534
                                              · linarith only [h14799, h18534, hlam]
                                              · linarith only [h17995, h18534, hlam]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h14799, h17994, h17998, h18470, h18472, h18478, h18480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h14799, h17994, h17998, h18472, h18473, h18478, hlam, p18518_2]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h17995, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18470, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18476, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h17995, h17998, h18473, h18480, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h14799, h17994, h18472, h18473, h18478, h18480, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18473, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18470, h18473, h18478, h18480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18518_1]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              rcases p18518_3 (m.d 0 3) (by simp) with h18548 | h18548
                                              · linarith only [h17998, h18548, hlam]
                                              · linarith only [h18468, h18548, hlam]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18468, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18474, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18478, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [h18480, hlam, p18518_0]
                                            · have p18518_0 := h18518c.1
                                              have p18518_1 := h18518c.2.1
                                              have p18518_2 := h18518c.2.2.1
                                              have p18518_3 := h18518c.2.2.2
                                              linarith only [hlam, p18518_0]
                                        · linarith only [h18515, hlam, p18481_0]
                                      · linarith only [h14799, h18514, hlam]
                                    · linarith only [h0, h18513, hlam]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h18471, hlam, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h18473, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  rcases p18481_3 (m.d 0 1) (by simp) with h18562 | h18562
                                  · linarith only [h16563, h18562, hlam]
                                  · linarith only [h17994, h18562, hlam]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h17994, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h18472, hlam, p18481_1]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h18474, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [h18475, hlam, p18481_0]
                                · have p18481_0 := h18481c.1
                                  have p18481_1 := h18481c.2.1
                                  have p18481_2 := h18481c.2.2.1
                                  have p18481_3 := h18481c.2.2.2
                                  linarith only [hlam, p18481_0]
                              · linarith only [h14799, h17994, h17998, h18469, h18472, h18478, h18480, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h14799, h17994, h17998, h18470, h18473, h18475, h18479, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h17998, h18468, h18470, h18473, h18478, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h16563, h18469, h18475, hlam]
                    · linarith only [h14799, h17998, h18473, h18474, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18575 | h18575
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18576 | h18576
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18577 | h18577
                        · linarith only [h0, h16563, h17994, h17995, h18472, h18473, h18577, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18579 | h18579
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18580 | h18580
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18581 | h18581
                              · rcases h1bigk with h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c | h18582c
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h0, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h14799, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h16563, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h14799, h18472, h18473, h18579, h18581, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  rcases p18582_3 (m.d 0 1) (by simp) with h18588 | h18588
                                  · linarith only [h18588, hlam, p18582_0]
                                  · rcases p18582_3 (m.d 1 2) (by simp) with h18590 | h18590
                                    · rcases p18582_3 (m.d 1 3) (by simp) with h18591 | h18591
                                      · linarith only [h18470, h18591, hlam]
                                      · linarith only [h14799, h18591, hlam]
                                    · linarith only [h18590, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h14799, h17994, h18472, h18473, h18579, h18581, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  rcases p18582_3 (m.d 0 1) (by simp) with h18598 | h18598
                                  · linarith only [h0, h18598, hlam]
                                  · linarith only [h17994, h18598, hlam]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h17994, h18472, h18473, h18579, h18581, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h18470, hlam, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h18473, hlam, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  rcases p18582_3 (m.d 0 1) (by simp) with h18605 | h18605
                                  · linarith only [h14799, h18605, hlam]
                                  · linarith only [h17994, h18605, hlam]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  rcases p18582_3 (m.d 0 1) (by simp) with h18608 | h18608
                                  · linarith only [h18608, hlam, p18582_0]
                                  · rcases p18582_3 (m.d 1 2) (by simp) with h18610 | h18610
                                    · rcases p18582_3 (m.d 1 3) (by simp) with h18611 | h18611
                                      · linarith only [h18473, h18611, hlam]
                                      · linarith only [h14799, h18611, hlam]
                                    · linarith only [h0, h18610, hlam]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h18471, hlam, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h14799, h17994, h18471, h18472, h18579, h18581, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  rcases p18582_3 (m.d 0 1) (by simp) with h18618 | h18618
                                  · linarith only [h16563, h18618, hlam]
                                  · linarith only [h17994, h18618, hlam]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h17994, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h18472, hlam, p18582_1]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h18575, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [h18576, hlam, p18582_0]
                                · have p18582_0 := h18582c.1
                                  have p18582_1 := h18582c.2.1
                                  have p18582_2 := h18582c.2.2.1
                                  have p18582_3 := h18582c.2.2.2
                                  linarith only [hlam, p18582_0]
                              · linarith only [h14799, h17994, h17998, h18469, h18472, h18579, h18581, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h14799, h17994, h18576, h18577, h18579, h18580, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h14799, h18468, h18473, h18579, hc23, hc34, hlam, hphi]
                      · linarith only [h16563, h18469, h18576, hlam]
                    · linarith only [h14799, h18468, h18575, hlam]
                · linarith only [h0, h17997, h18472, hlam]
              · linarith only [h0, h17996, h18471, hlam]
            · linarith only [h0, h17995, h18470, hlam]
          · linarith only [h16563, h17994, h18469, hlam]
        · linarith only [h14799, h17994, h18468, hlam]
    · linarith only [h0, h17994, h17997, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h18637 | h18637
    · rcases m.htr 0 3 4 (by decide) (by decide) with h18638 | h18638
      · linarith only [h17995, h17996, h18638, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18640 | h18640
        · rcases m.htr 0 4 5 (by decide) (by decide) with h18641 | h18641
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18642 | h18642
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18643 | h18643
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18644 | h18644
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18645 | h18645
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18646 | h18646
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18647 | h18647
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18648 | h18648
                        · linarith only [h14799, h17994, h17995, h18638, h18644, h18648, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18650 | h18650
                          · linarith only [h17995, h17996, h18642, h18645, h18648, h18650, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h17995, h17996, h18640, h18642, h18645, h18648, h18650, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h16563, h18641, h18647, hlam]
                    · linarith only [h14799, h17994, h18638, h18644, h18645, h18646, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18655 | h18655
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18656 | h18656
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18657 | h18657
                        · linarith only [h17995, h17996, h18643, h18645, h18657, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18659 | h18659
                          · linarith only [h17995, h17996, h18643, h18659, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h14799, h18640, h18645, h18659, hc23, hc34, hlam, hphi]
                      · linarith only [h16563, h18641, h18656, hlam]
                    · linarith only [h14799, h17995, h17996, h18640, h18643, h18655, hc01, hc12, hlam, hphi]
                · linarith only [h17996, h18643, h18644, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18665 | h18665
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18666 | h18666
                  · linarith only [h14799, h17994, h18638, h18642, h18643, h18665, h18666, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18668 | h18668
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18669 | h18669
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18670 | h18670
                        · linarith only [h0, h17995, h18643, h18666, h18670, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18672 | h18672
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18673 | h18673
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18674 | h18674
                              · rcases h1bigk with h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c | h18675c
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h0, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h14799, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h16563, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h0, h18643, h18665, h18670, h18672, h18674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18643, h18670, hc01, hc34, hlam, hphi, ht12, ht23, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h14799, h17994, h18643, h18665, h18670, h18672, h18674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18643, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  rcases p18675_3 (m.d 0 1) (by simp) with h18685 | h18685
                                  · linarith only [h0, h18685, hlam]
                                  · linarith only [h17994, h18685, hlam]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h17994, h18642, h18643, h18665, h18670, h18672, h18674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18642, hlam, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18666, hlam, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  rcases p18675_3 (m.d 0 1) (by simp) with h18692 | h18692
                                  · linarith only [h14799, h18692, hlam]
                                  · linarith only [h17994, h18692, hlam]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  rcases p18675_3 (m.d 0 1) (by simp) with h18695 | h18695
                                  · linarith only [h18695, hlam, p18675_0]
                                  · rcases p18675_3 (m.d 1 2) (by simp) with h18697 | h18697
                                    · linarith only [h18643, h18697, hlam]
                                    · linarith only [h0, h18697, hlam]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h0, h17994, h18643, h18665, h18670, h18672, h18674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h14799, h17994, h18643, h18665, h18670, h18672, h18674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  rcases p18675_3 (m.d 0 1) (by simp) with h18703 | h18703
                                  · linarith only [h16563, h18703, hlam]
                                  · linarith only [h17994, h18703, hlam]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h17994, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18665, hlam, p18675_1]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18668, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [h18669, hlam, p18675_0]
                                · have p18675_0 := h18675c.1
                                  have p18675_1 := h18675c.2.1
                                  have p18675_2 := h18675c.2.2.1
                                  have p18675_3 := h18675c.2.2.2
                                  linarith only [hlam, p18675_0]
                              · linarith only [h17995, h17996, h18670, h18674, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h14799, h17994, h18642, h18643, h18669, h18673, hlam]
                          · linarith only [h0, h17995, h18640, h18643, h18670, h18672, hc23, hc34, hlam, hphi]
                      · linarith only [h16563, h17994, h18641, h18665, h18669, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h14799, h17994, h17995, h18640, h18665, h18668, hc02, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h18637, h18665, hlam]
            · linarith only [h0, h17995, h18642, hlam]
          · linarith only [h0, h17994, h17996, h18641, hlam]
        · linarith only [h14799, h17994, h18640, hlam]
    · linarith only [h14799, h17994, h17995, h18637, hlam]

end R2N4
