import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S29

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h17539 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 3 (by decide) (by decide) with h17989 | h17989
  · rcases m.htr 0 2 4 (by decide) (by decide) with h17990 | h17990
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17991 | h17991
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17992 | h17992
        · linarith only [h15532, h15533, h17992, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17994 | h17994
          · linarith only [h15532, h17539, h17994, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17996 | h17996
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17997 | h17997
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17998 | h17998
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17999 | h17999
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18000 | h18000
                    · linarith only [h15532, h15533, h17992, h17998, h18000, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18002 | h18002
                      · linarith only [h15532, h17539, h17994, h18002, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18004 | h18004
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18005 | h18005
                          · linarith only [h15532, h17539, h17989, h18000, h18004, h18005, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18007 | h18007
                            · linarith only [h15532, h17539, h17997, h18002, h18007, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18009 | h18009
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18010 | h18010
                                · rcases h0bigk with h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c | h18011c
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [hlam, p18011_0]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h0, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h15532, h17539, h17997, h18000, h18004, hc23, hc34, hlam, hphi, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h15533, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17539, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    rcases p18011_3 (m.d 0 1) (by simp) with h18017 | h18017
                                    · linarith only [h0, h18017, hlam]
                                    · rcases p18011_3 (m.d 0 2) (by simp) with h18019 | h18019
                                      · rcases p18011_3 (m.d 0 3) (by simp) with h18020 | h18020
                                        · linarith only [h17989, h18020, hlam]
                                        · rcases p18011_3 (m.d 0 4) (by simp) with h18022 | h18022
                                          · linarith only [h17990, h18022, hlam]
                                          · linarith only [h15533, h18022, hlam]
                                      · linarith only [h0, h18019, hlam]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [hlam, p18011_0]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    rcases p18011_3 (m.d 0 1) (by simp) with h18027 | h18027
                                    · linarith only [h0, h18027, hlam]
                                    · linarith only [h15532, h18027, hlam]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    rcases p18011_3 (m.d 0 1) (by simp) with h18030 | h18030
                                    · linarith only [h0, h18030, hlam]
                                    · rcases p18011_3 (m.d 0 2) (by simp) with h18032 | h18032
                                      · rcases p18011_3 (m.d 0 3) (by simp) with h18033 | h18033
                                        · linarith only [h17989, h18033, hlam]
                                        · rcases p18011_3 (m.d 0 4) (by simp) with h18035 | h18035
                                          · linarith only [h17990, h18035, hlam]
                                          · rcases p18011_3 (m.d 0 5) (by simp) with h18037 | h18037
                                            · linarith only [h17991, h18037, hlam]
                                            · rcases h2bigk with h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c | h18039c
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h0, hlam, p18039_1]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h15532, h17539, h17996, h17997, hlam, p18011_1, p18039_2]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                rcases p18039_3 (m.d 0 2) (by simp) with h18043 | h18043
                                                · rcases p18039_3 (m.d 1 2) (by simp) with h18044 | h18044
                                                  · rcases p18039_3 (m.d 2 3) (by simp) with h18045 | h18045
                                                    · linarith only [h17989, h18045, hlam]
                                                    · rcases p18039_3 (m.d 2 4) (by simp) with h18047 | h18047
                                                      · linarith only [h18047, hlam, p18039_0]
                                                      · rcases p18039_3 (m.d 2 5) (by simp) with h18049 | h18049
                                                        · linarith only [h17991, h18049, hlam]
                                                        · rcases h3bigk with h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c | h18051c
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h0, h15532, h17539, h17996, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18011_1, p18051_1]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h0, h15532, h17539, h17996, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18011_1, p18051_1]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h17992, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h17994, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h15532, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h0, h15532, h17539, h17996, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18011_1, p18051_1]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h18000, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h18002, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h17989, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h17997, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h18005, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h18007, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            rcases p18051_3 (m.d 0 3) (by simp) with h18067 | h18067
                                                            · linarith only [h18067, hlam, p18051_0]
                                                            · rcases p18051_3 (m.d 1 3) (by simp) with h18069 | h18069
                                                              · linarith only [h18000, h18069, hlam]
                                                              · rcases p18051_3 (m.d 2 3) (by simp) with h18071 | h18071
                                                                · linarith only [h18005, h18071, hlam]
                                                                · rcases p18051_3 (m.d 3 4) (by simp) with h18073 | h18073
                                                                  · rcases p18051_3 (m.d 3 5) (by simp) with h18074 | h18074
                                                                    · linarith only [h18010, h18074, hlam]
                                                                    · linarith only [h17994, h18074, hlam]
                                                                  · linarith only [h18073, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            rcases p18051_3 (m.d 0 3) (by simp) with h18078 | h18078
                                                            · linarith only [h17992, h18078, hlam]
                                                            · linarith only [h15532, h18078, hlam]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            rcases p18051_3 (m.d 0 3) (by simp) with h18081 | h18081
                                                            · linarith only [h17992, h18081, hlam]
                                                            · linarith only [h17989, h18081, hlam]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h17539, h18002, hc01, hc34, hlam, hphi, ht12, ht23, p18051_1]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            rcases p18051_3 (m.d 0 3) (by simp) with h18086 | h18086
                                                            · linarith only [h18086, hlam, p18051_0]
                                                            · rcases p18051_3 (m.d 1 3) (by simp) with h18088 | h18088
                                                              · linarith only [h18002, h18088, hlam]
                                                              · rcases p18051_3 (m.d 2 3) (by simp) with h18090 | h18090
                                                                · linarith only [h18007, h18090, hlam]
                                                                · rcases p18051_3 (m.d 3 4) (by simp) with h18092 | h18092
                                                                  · rcases p18051_3 (m.d 3 5) (by simp) with h18093 | h18093
                                                                    · rcases h5bigk with h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c | h18094c
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h17539, hlam, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h0, h17996, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18011_1, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h17994, hlam, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h0, h17996, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18011_1, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h15532, h17539, h17997, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18002, h18007, h18010, hc23, hc34, hlam, hphi, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18002, hlam, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        rcases p18094_3 (m.d 0 5) (by simp) with h18104 | h18104
                                                                        · linarith only [h17539, h18104, hlam]
                                                                        · linarith only [h17996, h18104, hlam]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h17991, hlam, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h17999, hlam, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18007, hlam, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h17991, hc02, hc45, hlam, hphi, ht0b, ht5b, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h15532, h17539, h17997, h18010, hc23, hc34, hlam, hphi, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h15532, h17539, h17997, h18010, hc23, hc34, hlam, hphi, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18007, h18010, hc23, hc34, hlam, hphi, p18094_1]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        rcases p18094_3 (m.d 0 5) (by simp) with h18116 | h18116
                                                                        · linarith only [h17994, h18116, hlam]
                                                                        · linarith only [h17996, h18116, hlam]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h17996, hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18004, hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18009, hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [h18010, hlam, p18094_0]
                                                                      · have p18094_0 := h18094c.1
                                                                        have p18094_1 := h18094c.2.1
                                                                        have p18094_2 := h18094c.2.2.1
                                                                        have p18094_3 := h18094c.2.2.2
                                                                        linarith only [hlam, p18094_0]
                                                                    · linarith only [h18093, hlam, p18051_0]
                                                                  · linarith only [h17992, h18092, hlam]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            rcases p18051_3 (m.d 0 3) (by simp) with h18126 | h18126
                                                            · linarith only [h17994, h18126, hlam]
                                                            · linarith only [h15532, h18126, hlam]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            rcases p18051_3 (m.d 0 3) (by simp) with h18129 | h18129
                                                            · linarith only [h17994, h18129, hlam]
                                                            · linarith only [h17989, h18129, hlam]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [h18010, hlam, p18051_0]
                                                          · have p18051_0 := h18051c.1
                                                            have p18051_1 := h18051c.2.1
                                                            have p18051_2 := h18051c.2.2.1
                                                            have p18051_3 := h18051c.2.2.2
                                                            linarith only [hlam, p18051_0]
                                                  · linarith only [h17998, h18044, hlam]
                                                · linarith only [h18043, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                rcases p18039_3 (m.d 0 2) (by simp) with h18136 | h18136
                                                · rcases p18039_3 (m.d 1 2) (by simp) with h18137 | h18137
                                                  · rcases p18039_3 (m.d 2 3) (by simp) with h18138 | h18138
                                                    · linarith only [h17989, h18138, hlam]
                                                    · rcases p18039_3 (m.d 2 4) (by simp) with h18140 | h18140
                                                      · linarith only [h17990, h18140, hlam]
                                                      · linarith only [h18009, h18140, hlam]
                                                  · linarith only [h17999, h18137, hlam]
                                                · linarith only [h18136, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h15532, h17539, h17996, h17997, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18011_1, p18039_1]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h0, h15532, h17539, h17996, h17997, hlam, p18011_1, p18039_2]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                rcases p18039_3 (m.d 0 2) (by simp) with h18148 | h18148
                                                · linarith only [h0, h18148, hlam]
                                                · linarith only [h17990, h18148, hlam]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                rcases p18039_3 (m.d 0 2) (by simp) with h18151 | h18151
                                                · linarith only [h0, h18151, hlam]
                                                · linarith only [h17991, h18151, hlam]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17989, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17997, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h18005, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h18007, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17990, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17998, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17990, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p18011_1, p18039_1]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h0, h17990, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18011_1, p18039_1]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17991, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h17999, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h0, h17991, h17996, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18011_1, p18039_1]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [h18009, hlam, p18039_0]
                                              · have p18039_0 := h18039c.1
                                                have p18039_1 := h18039c.2.1
                                                have p18039_2 := h18039c.2.2.1
                                                have p18039_3 := h18039c.2.2.2
                                                linarith only [hlam, p18039_0]
                                      · linarith only [h17990, h18032, hlam]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    rcases p18011_3 (m.d 0 1) (by simp) with h18170 | h18170
                                    · linarith only [h0, h18170, hlam]
                                    · rcases p18011_3 (m.d 0 2) (by simp) with h18172 | h18172
                                      · rcases p18011_3 (m.d 0 3) (by simp) with h18173 | h18173
                                        · linarith only [h17989, h18173, hlam]
                                        · rcases p18011_3 (m.d 0 4) (by simp) with h18175 | h18175
                                          · linarith only [h17990, h18175, hlam]
                                          · linarith only [h17996, h18175, hlam]
                                      · linarith only [h17991, h18172, hlam]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h15532, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17989, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [hlam, p18011_0]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17992, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17994, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h15532, h15533, h17997, h18000, hc23, hc34, hlam, hphi, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17990, hlam, p18011_0]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    rcases p18011_3 (m.d 0 1) (by simp) with h18186 | h18186
                                    · linarith only [h15533, h18186, hlam]
                                    · linarith only [h15532, h18186, hlam]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [hlam, p18011_0]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h15532, h15533, h17539, h17997, h18000, hc23, hc34, hlam, hphi, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h15532, h17994, h17997, h18010, hc23, hc34, hlam, hphi, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17991, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    rcases p18011_3 (m.d 0 1) (by simp) with h18193 | h18193
                                    · linarith only [h17539, h18193, hlam]
                                    · linarith only [h15532, h18193, hlam]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [h17996, hlam, p18011_1]
                                  · have p18011_0 := h18011c.1
                                    have p18011_1 := h18011c.2.1
                                    have p18011_2 := h18011c.2.2.1
                                    have p18011_3 := h18011c.2.2.2
                                    linarith only [hlam, p18011_0]
                                · linarith only [h15532, h15533, h17997, h18000, h18010, hc23, hc45, hlam, hphi, ht34]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18199 | h18199
                                · rcases h0bigk with h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c | h18200c
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [hlam, p18200_0]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h0, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h15532, h17539, h17997, h18000, h18004, hc23, hc34, hlam, hphi, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h15533, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17539, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    rcases p18200_3 (m.d 0 1) (by simp) with h18206 | h18206
                                    · linarith only [h0, h18206, hlam]
                                    · rcases p18200_3 (m.d 0 2) (by simp) with h18208 | h18208
                                      · rcases p18200_3 (m.d 0 3) (by simp) with h18209 | h18209
                                        · linarith only [h17989, h18209, hlam]
                                        · rcases p18200_3 (m.d 0 4) (by simp) with h18211 | h18211
                                          · linarith only [h17990, h18211, hlam]
                                          · linarith only [h15533, h18211, hlam]
                                      · linarith only [h0, h18208, hlam]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [hlam, p18200_0]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    rcases p18200_3 (m.d 0 1) (by simp) with h18216 | h18216
                                    · linarith only [h0, h18216, hlam]
                                    · linarith only [h15532, h18216, hlam]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h0, h17996, h18009, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    rcases p18200_3 (m.d 0 1) (by simp) with h18220 | h18220
                                    · linarith only [h0, h18220, hlam]
                                    · rcases p18200_3 (m.d 0 2) (by simp) with h18222 | h18222
                                      · rcases p18200_3 (m.d 0 3) (by simp) with h18223 | h18223
                                        · linarith only [h17989, h18223, hlam]
                                        · rcases p18200_3 (m.d 0 4) (by simp) with h18225 | h18225
                                          · linarith only [h17990, h18225, hlam]
                                          · linarith only [h17996, h18225, hlam]
                                      · linarith only [h17991, h18222, hlam]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h15532, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17989, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [hlam, p18200_0]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17992, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17994, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h15532, h15533, h17997, h18000, hc23, hc34, hlam, hphi, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17990, hlam, p18200_0]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    rcases p18200_3 (m.d 0 1) (by simp) with h18236 | h18236
                                    · linarith only [h15533, h18236, hlam]
                                    · linarith only [h15532, h18236, hlam]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [hlam, p18200_0]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h15532, h15533, h17539, h17997, h18000, hc23, hc34, hlam, hphi, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h15532, h17539, h17997, h18000, h18004, hc23, hc34, hlam, hphi, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17991, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    rcases p18200_3 (m.d 0 1) (by simp) with h18243 | h18243
                                    · linarith only [h17539, h18243, hlam]
                                    · linarith only [h15532, h18243, hlam]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [h17996, hlam, p18200_1]
                                  · have p18200_0 := h18200c.1
                                    have p18200_1 := h18200c.2.1
                                    have p18200_2 := h18200c.2.2.1
                                    have p18200_3 := h18200c.2.2.2
                                    linarith only [hlam, p18200_0]
                                · linarith only [h15532, h15533, h17997, h18000, h18199, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h15533, h17996, h18004, hlam]
                  · linarith only [h0, h17991, h17999, hlam]
                · linarith only [h0, h17990, h17998, hlam]
              · linarith only [h0, h17989, h17997, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18253 | h18253
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18254 | h18254
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18255 | h18255
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18256 | h18256
                    · linarith only [h15532, h15533, h17996, h18256, hc34, hc45, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18258 | h18258
                      · linarith only [h15532, h15533, h17994, h17996, h18258, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18260 | h18260
                        · linarith only [h15532, h15533, h17996, h18256, h18260, hc13, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h18253, h18260, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h17991, h18255, hlam]
                · linarith only [h0, h17990, h18254, hlam]
              · linarith only [h0, h17989, h18253, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18266 | h18266
        · linarith only [h15532, h15533, h18266, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h18268 | h18268
          · linarith only [h0, h15532, h17991, h18268, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18270 | h18270
            · linarith only [h17990, h17991, h18270, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18272 | h18272
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18273 | h18273
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18274 | h18274
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18275 | h18275
                    · linarith only [h15532, h15533, h17990, h17991, h18266, h18274, h18275, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18277 | h18277
                      · linarith only [h15532, h15533, h17990, h17991, h18268, h18277, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18279 | h18279
                        · linarith only [h15532, h15533, h18270, h18275, h18279, hc13, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h18272, h18279, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18282 | h18282
                    · linarith only [h0, h15532, h18274, h18282, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18284 | h18284
                      · linarith only [h15532, h15533, h18273, h18274, h18284, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18286 | h18286
                        · linarith only [h15532, h15533, h18270, h18272, h18273, h18274, h18286, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h15532, h15533, h18272, h18286, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h15532, h17990, h18272, h18273, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h17989, h18272, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h18291 | h18291
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18292 | h18292
        · linarith only [h0, h15532, h17990, h18292, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h18294 | h18294
          · linarith only [h15532, h17539, h18294, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18296 | h18296
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18297 | h18297
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18298 | h18298
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18299 | h18299
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18300 | h18300
                    · linarith only [h15532, h17539, h17990, h18291, h18292, h18298, h18300, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18302 | h18302
                      · linarith only [h15532, h17539, h18294, h18302, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18304 | h18304
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18305 | h18305
                          · linarith only [h15532, h17539, h17990, h18291, h18297, h18298, h18300, h18305, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18307 | h18307
                            · linarith only [h15532, h17539, h17990, h18291, h18297, h18298, h18307, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18309 | h18309
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18310 | h18310
                                · rcases h0bigk with h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c | h18311c
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [hlam, p18311_0]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h0, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, h17539, h17990, h18291, h18297, h18298, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15533, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h17539, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h17990, h18298, hc01, hc12, hlam, hphi, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [hlam, p18311_0]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, h17990, h18297, h18298, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h17990, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h17990, h18298, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h17989, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [hlam, p18311_0]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h18292, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h18294, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, h15533, h18297, h18300, hc23, hc34, hlam, hphi, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h0, h15532, h17990, h18297, h18298, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    rcases p18311_3 (m.d 0 1) (by simp) with h18329 | h18329
                                    · linarith only [h15533, h18329, hlam]
                                    · linarith only [h15532, h18329, hlam]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [hlam, p18311_0]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, h17539, h17990, h18297, h18298, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, h17539, h18297, h18300, h18304, hc23, hc34, hlam, hphi, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h18291, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h15532, h17990, h18291, h18297, h18298, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [h18296, hlam, p18311_1]
                                  · have p18311_0 := h18311c.1
                                    have p18311_1 := h18311c.2.1
                                    have p18311_2 := h18311c.2.2.1
                                    have p18311_3 := h18311c.2.2.2
                                    linarith only [hlam, p18311_0]
                                · linarith only [h15532, h15533, h18297, h18300, h18310, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h17990, h18291, h18296, h18309, hlam]
                        · linarith only [h17990, h18291, h18296, h18298, h18304, hlam]
                  · linarith only [h17990, h18291, h18298, h18299, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18343 | h18343
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18344 | h18344
                    · linarith only [h0, h15532, h18292, h18298, h18344, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18346 | h18346
                      · linarith only [h15532, h17539, h18298, h18343, h18346, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18348 | h18348
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18349 | h18349
                          · linarith only [h15532, h17539, h18297, h18298, h18343, h18344, h18349, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h15532, h17539, h18297, h18298, h18343, h18349, hc23, hc34, hlam, hphi]
                        · linarith only [h15532, h17539, h18296, h18297, h18298, h18343, h18348, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h15532, h18291, h18297, h18343, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h17989, h18297, hlam]
            · linarith only [h17990, h18291, h18296, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18356 | h18356
        · linarith only [h0, h15532, h17990, h18356, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h18358 | h18358
          · linarith only [h15532, h17539, h18358, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h18360 | h18360
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18361 | h18361
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18362 | h18362
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18363 | h18363
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18364 | h18364
                    · linarith only [h0, h15532, h17990, h18356, h18362, h18364, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18366 | h18366
                      · linarith only [h0, h15532, h18291, h18358, h18366, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18368 | h18368
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18369 | h18369
                          · linarith only [h17989, h18291, h18363, h18364, h18368, h18369, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18371 | h18371
                            · linarith only [h0, h15532, h18291, h18361, h18363, h18366, h18371, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h18373 | h18373
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h18374 | h18374
                                · rcases h0bigk with h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c | h18375c
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [hlam, p18375_0]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h0, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h0, h18291, h18362, h18373, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h15533, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h17539, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h18291, h18362, h18373, hc01, hc12, hlam, hphi, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [hlam, p18375_0]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h15532, h18291, h18361, h18362, h18373, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h17990, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h18291, hlam, p18375_0]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h15532, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h17989, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [hlam, p18375_0]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h18356, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h18358, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h15532, h15533, h18361, h18364, hc23, hc34, hlam, hphi, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h0, h15532, h17990, h18361, h18362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    rcases p18375_3 (m.d 0 1) (by simp) with h18393 | h18393
                                    · linarith only [h15533, h18393, hlam]
                                    · linarith only [h15532, h18393, hlam]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [hlam, p18375_0]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h15532, h17539, h17990, h18361, h18362, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h15532, h17539, h18361, h18366, hc23, hc35, hlam, hphi, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h0, h15532, h18291, h18361, h18362, h18373, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    rcases p18375_3 (m.d 0 1) (by simp) with h18400 | h18400
                                    · linarith only [h17539, h18400, hlam]
                                    · linarith only [h15532, h18400, hlam]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [h18360, hlam, p18375_1]
                                  · have p18375_0 := h18375c.1
                                    have p18375_1 := h18375c.2.1
                                    have p18375_2 := h18375c.2.2.1
                                    have p18375_3 := h18375c.2.2.2
                                    linarith only [hlam, p18375_0]
                                · linarith only [h15532, h15533, h17990, h18360, h18361, h18362, h18364, h18374, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h17990, h18360, h18373, hlam]
                        · linarith only [h15532, h15533, h18360, h18361, h18368, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h15532, h17990, h18361, h18362, h18363, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18409 | h18409
                  · linarith only [h0, h15532, h18291, h18361, h18362, h18409, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18411 | h18411
                    · linarith only [h0, h15532, h18356, h18362, h18411, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18413 | h18413
                      · linarith only [h0, h15532, h18362, h18413, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18415 | h18415
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18416 | h18416
                          · linarith only [h0, h15532, h17989, h18291, h18360, h18409, h18411, h18415, h18416, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h15532, h18361, h18362, h18416, hc23, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h18361, h18415, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h17989, h18361, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18421 | h18421
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18422 | h18422
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18423 | h18423
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18424 | h18424
                    · linarith only [h15532, h15533, h18360, h18424, hc34, hc45, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18426 | h18426
                      · linarith only [h0, h15532, h17990, h18422, h18426, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18428 | h18428
                        · linarith only [h0, h15532, h17990, h18360, h18421, h18424, h18428, hc23, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h18421, h18428, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h15532, h17990, h18421, h18422, h18423, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h18432 | h18432
                  · linarith only [h0, h15532, h18291, h18421, h18422, h18432, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18434 | h18434
                    · linarith only [h0, h15532, h18422, h18434, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18436 | h18436
                      · linarith only [h0, h15532, h18422, h18436, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18438 | h18438
                        · linarith only [h0, h15532, h17990, h18360, h18421, h18434, h18438, hc23, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h18421, h18438, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h15532, h17989, h18421, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · linarith only [h0, h15532, h17989, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 1 5 (by decide) (by decide) with h17539 | h17539
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h17539
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h17539

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 1 4 (by decide) (by decide) with h15533 | h15533
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533

end R2N4
