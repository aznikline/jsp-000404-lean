import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S44
import Jsp000404.R1LeavesN7_2S46

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  rcases m.htr 0 2 4 (by decide) (by decide) with h20000 | h20000
  · rcases m.htr 0 2 5 (by decide) (by decide) with h20001 | h20001
    · rcases m.htr 0 3 4 (by decide) (by decide) with h20002 | h20002
      · rcases m.htr 0 3 5 (by decide) (by decide) with h20003 | h20003
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20004 | h20004
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20005 | h20005
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20006 | h20006
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20007 | h20007
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20008 | h20008
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20009 | h20009
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20010 | h20010
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20011 | h20011
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20012 | h20012
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20013 | h20013
                            · linarith only [h18816, h20000, h20005, h20013, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h18816, h20000, h20004, h20005, h20013, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h16915, h18815, h18816, h20000, h20003, h20012, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h16915, h18815, h18816, h20000, h20002, h20011, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h16915, h18815, h20000, h20004, h20007, h20010, hc02, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h14396, h20003, h20009, hlam]
                  · linarith only [h18816, h20000, h20002, h20005, h20008, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h16915, h18815, h18816, h20000, h20005, h20007, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h18816, h20000, h20005, h20006, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20023 | h20023
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20024 | h20024
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20025 | h20025
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20026 | h20026
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20027 | h20027
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20028 | h20028
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20029 | h20029
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20030 | h20030
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20031 | h20031
                              · rcases h0bigk with h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c | h20032c
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h0, hlam, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h14396, hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h16915, hlam, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h16915, h20005, h20023, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h0, h20005, hc01, hc23, hlam, hphi, ht12, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h18816, hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h0, h16915, h18815, h20005, h20024, h20029, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  rcases p20032_3 (m.d 0 1) (by simp) with h20042 | h20042
                                  · linarith only [h0, h20042, hlam]
                                  · linarith only [h18815, h20042, hlam]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  rcases p20032_3 (m.d 0 1) (by simp) with h20045 | h20045
                                  · linarith only [h14396, h20045, hlam]
                                  · rcases p20032_3 (m.d 0 2) (by simp) with h20047 | h20047
                                    · linarith only [h18816, h20047, hlam]
                                    · linarith only [h0, h20047, hlam]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h14396, h20000, h20005, h20028, h20031, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  rcases p20032_3 (m.d 0 1) (by simp) with h20052 | h20052
                                  · linarith only [h14396, h20052, hlam]
                                  · rcases p20032_3 (m.d 0 2) (by simp) with h20054 | h20054
                                    · linarith only [h18816, h20054, hlam]
                                    · linarith only [h20000, h20054, hlam]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  rcases p20032_3 (m.d 0 1) (by simp) with h20057 | h20057
                                  · linarith only [h14396, h20057, hlam]
                                  · linarith only [h18815, h20057, hlam]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h16915, h18815, h20005, h20023, h20024, h20029, h20031, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h20000, hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h20002, hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  rcases p20032_3 (m.d 0 1) (by simp) with h20064 | h20064
                                  · linarith only [h16915, h20064, hlam]
                                  · linarith only [h18815, h20064, hlam]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h18815, hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h20001, hlam, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h20003, hlam, p20032_0]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [h20004, hlam, p20032_1]
                                · have p20032_0 := h20032c.1
                                  have p20032_1 := h20032c.2.1
                                  have p20032_2 := h20032c.2.2.1
                                  have p20032_3 := h20032c.2.2.2
                                  linarith only [hlam, p20032_0]
                              · linarith only [h0, h18815, h20005, h20027, h20031, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h16915, h18815, h20005, h20023, h20027, h20030, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h16915, h20005, h20023, h20029, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h16915, h20005, h20023, h20028, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h16915, h18815, h20000, h20004, h20026, h20027, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h14396, h20003, h20026, hlam]
                  · linarith only [h14396, h20002, h20025, hlam]
                · linarith only [h0, h20001, h20024, hlam]
              · linarith only [h0, h20000, h20023, hlam]
          · linarith only [h16915, h18815, h20004, hlam]
        · linarith only [h0, h18815, h18816, h20003, hlam]
      · linarith only [h18816, h20000, h20002, hlam]
    · linarith only [h16915, h18815, h20000, h20001, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h20085 | h20085
    · rcases m.htr 0 3 4 (by decide) (by decide) with h20086 | h20086
      · rcases m.htr 0 3 5 (by decide) (by decide) with h20087 | h20087
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20088 | h20088
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20089 | h20089
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20090 | h20090
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20091 | h20091
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20092 | h20092
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20093 | h20093
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20094 | h20094
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20095 | h20095
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20096 | h20096
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20097 | h20097
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20098 | h20098
                              · rcases h0bigk with h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c | h20099c
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h0, hlam, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h14396, hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h16915, hlam, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h0, h20000, h20089, h20095, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h20000, h20089, h20095, hc01, hc12, hlam, hphi, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h18816, hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h20000, hlam, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h18815, h20000, h20089, h20091, h20095, h20096, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h18815, h18816, h20089, h20091, h20096, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h0, h18815, h18816, h20089, h20091, h20096, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h16915, h18815, h18816, h20089, h20091, h20096, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  rcases p20099_3 (m.d 0 1) (by simp) with h20114 | h20114
                                  · linarith only [h14396, h20114, hlam]
                                  · linarith only [h18815, h20114, hlam]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h18815, h20000, h20089, h20091, h20095, h20096, h20098, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h0, h18815, h20000, h20089, h20091, h20095, h20096, h20098, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h20086, hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  rcases p20099_3 (m.d 0 1) (by simp) with h20121 | h20121
                                  · linarith only [h16915, h20121, hlam]
                                  · linarith only [h18815, h20121, hlam]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h18815, hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h20085, hlam, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h20087, hlam, p20099_0]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [h20088, hlam, p20099_1]
                                · have p20099_0 := h20099c.1
                                  have p20099_1 := h20099c.2.1
                                  have p20099_2 := h20099c.2.2.1
                                  have p20099_3 := h20099c.2.2.2
                                  linarith only [hlam, p20099_0]
                              · linarith only [h0, h18815, h20000, h20089, h20094, h20095, h20098, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h18815, h20000, h20094, h20097, hlam]
                          · linarith only [h18816, h20087, h20096, hlam]
                        · linarith only [h18816, h20086, h20095, hlam]
                      · linarith only [h20000, h20088, h20090, h20094, hlam]
                    · linarith only [h18816, h20087, h20089, h20093, hlam]
                  · linarith only [h18816, h20086, h20089, h20092, hlam]
                · linarith only [h18816, h20085, h20091, hc12, hc23, hlam, hphi]
              · linarith only [h0, h18816, h20089, h20090, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20138 | h20138
              · linarith only [h0, h18815, h20000, h20089, h20138, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20140 | h20140
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20141 | h20141
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20142 | h20142
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20143 | h20143
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20144 | h20144
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20145 | h20145
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20146 | h20146
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20147 | h20147
                              · rcases h0bigk with h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c | h20148c
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h0, hlam, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h14396, hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h16915, hlam, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h0, h20138, h20144, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h0, h20138, h20144, hc01, hc23, hlam, hphi, ht12, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h18816, hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h20000, hlam, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20158 | h20158
                                  · linarith only [h0, h20158, hlam]
                                  · linarith only [h18815, h20158, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20161 | h20161
                                  · linarith only [h14396, h20161, hlam]
                                  · rcases p20148_3 (m.d 0 2) (by simp) with h20163 | h20163
                                    · linarith only [h18816, h20163, hlam]
                                    · linarith only [h0, h20163, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20166 | h20166
                                  · linarith only [h14396, h20166, hlam]
                                  · rcases p20148_3 (m.d 0 2) (by simp) with h20168 | h20168
                                    · linarith only [h18816, h20168, hlam]
                                    · rcases p20148_3 (m.d 0 3) (by simp) with h20170 | h20170
                                      · rcases p20148_3 (m.d 0 4) (by simp) with h20171 | h20171
                                        · linarith only [h20086, h20171, hlam]
                                        · linarith only [h20000, h20171, hlam]
                                      · linarith only [h18816, h20170, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20176 | h20176
                                  · linarith only [h14396, h20176, hlam]
                                  · rcases p20148_3 (m.d 0 2) (by simp) with h20178 | h20178
                                    · linarith only [h18816, h20178, hlam]
                                    · rcases p20148_3 (m.d 0 3) (by simp) with h20180 | h20180
                                      · rcases p20148_3 (m.d 0 4) (by simp) with h20181 | h20181
                                        · linarith only [h20086, h20181, hlam]
                                        · rcases p20148_3 (m.d 0 5) (by simp) with h20183 | h20183
                                          · linarith only [h20087, h20183, hlam]
                                          · rcases h2bigk with h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c | h20185c
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h0, hlam, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h18816, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20000, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h14396, h20000, h20089, h20145, h20147, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20148_1, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20138, h20144, hc02, hc23, hlam, hphi, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20089, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20138, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              rcases p20185_3 (m.d 0 2) (by simp) with h20195 | h20195
                                              · linarith only [h0, h20195, hlam]
                                              · linarith only [h20085, h20195, hlam]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              rcases p20185_3 (m.d 0 2) (by simp) with h20198 | h20198
                                              · linarith only [h20198, hlam, p20185_0]
                                              · rcases p20185_3 (m.d 1 2) (by simp) with h20200 | h20200
                                                · linarith only [h20089, h20200, hlam]
                                                · linarith only [h0, h20200, hlam]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h0, h18815, h20140, h20145, h20147, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h0, h18815, h20000, h20140, h20145, h20147, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h14396, h16915, h18815, h20089, h20140, hlam, p20148_1, p20185_2]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              rcases p20185_3 (m.d 0 2) (by simp) with h20207 | h20207
                                              · linarith only [h20207, hlam, p20185_0]
                                              · rcases p20185_3 (m.d 1 2) (by simp) with h20209 | h20209
                                                · linarith only [h20138, h20209, hlam]
                                                · linarith only [h0, h20209, hlam]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20144, hlam, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h0, h18815, h20138, h20140, hlam, p20185_2]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20085, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20140, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20145, hlam, p20185_1]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [h20146, hlam, p20185_0]
                                            · have p20185_0 := h20185c.1
                                              have p20185_1 := h20185c.2.1
                                              have p20185_2 := h20185c.2.2.1
                                              have p20185_3 := h20185c.2.2.2
                                              linarith only [hlam, p20185_0]
                                      · linarith only [h20086, h20180, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20222 | h20222
                                  · linarith only [h14396, h20222, hlam]
                                  · linarith only [h18815, h20222, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20225 | h20225
                                  · linarith only [h16915, h20225, hlam]
                                  · rcases p20148_3 (m.d 0 2) (by simp) with h20227 | h20227
                                    · linarith only [h20000, h20227, hlam]
                                    · linarith only [h0, h20227, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20230 | h20230
                                  · linarith only [h16915, h20230, hlam]
                                  · rcases p20148_3 (m.d 0 2) (by simp) with h20232 | h20232
                                    · linarith only [h20000, h20232, hlam]
                                    · rcases p20148_3 (m.d 0 3) (by simp) with h20234 | h20234
                                      · rcases p20148_3 (m.d 0 4) (by simp) with h20235 | h20235
                                        · rcases p20148_3 (m.d 0 5) (by simp) with h20236 | h20236
                                          · linarith only [h20088, h20236, hlam]
                                          · rcases h2bigk with h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c | h20238c
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h0, hlam, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h18816, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20000, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20145, h20147, hc04, hc45, hlam, hphi, ht0b, ht5b, p20148_1, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20089, hc02, hc23, hlam, hphi, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20089, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20138, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              rcases p20238_3 (m.d 0 2) (by simp) with h20248 | h20248
                                              · linarith only [h0, h20248, hlam]
                                              · linarith only [h20085, h20248, hlam]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              rcases p20238_3 (m.d 0 2) (by simp) with h20251 | h20251
                                              · linarith only [h20251, hlam, p20238_0]
                                              · rcases p20238_3 (m.d 1 2) (by simp) with h20253 | h20253
                                                · linarith only [h20089, h20253, hlam]
                                                · linarith only [h0, h20253, hlam]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h0, h18815, h20140, h20145, h20147, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h0, h18815, h20000, h20140, h20145, h20147, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h0, h14396, h18815, h20086, h20089, h20140, hlam, p20148_1, p20238_2]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              rcases p20238_3 (m.d 0 2) (by simp) with h20260 | h20260
                                              · linarith only [h20260, hlam, p20238_0]
                                              · rcases p20238_3 (m.d 1 2) (by simp) with h20262 | h20262
                                                · linarith only [h20138, h20262, hlam]
                                                · linarith only [h0, h20262, hlam]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h0, h20144, hc01, hc23, hlam, hphi, ht12, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20144, hlam, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h0, h18815, h20000, h20140, hlam, p20148_1, p20238_2]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20085, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20140, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20145, hlam, p20238_1]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [h20146, hlam, p20238_0]
                                            · have p20238_0 := h20238c.1
                                              have p20238_1 := h20238c.2.1
                                              have p20238_2 := h20238c.2.2.1
                                              have p20238_3 := h20238c.2.2.2
                                              linarith only [hlam, p20238_0]
                                        · linarith only [h20000, h20235, hlam]
                                      · linarith only [h18816, h20234, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h20086, hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  rcases p20148_3 (m.d 0 1) (by simp) with h20278 | h20278
                                  · linarith only [h16915, h20278, hlam]
                                  · linarith only [h18815, h20278, hlam]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h18815, hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h20085, hlam, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h20087, hlam, p20148_0]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [h20088, hlam, p20148_1]
                                · have p20148_0 := h20148c.1
                                  have p20148_1 := h20148c.2.1
                                  have p20148_2 := h20148c.2.2.1
                                  have p20148_3 := h20148c.2.2.2
                                  linarith only [hlam, p20148_0]
                              · linarith only [h0, h18815, h20138, h20143, h20147, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h18815, h20138, h20143, h20146, hlam]
                          · linarith only [h0, h20138, h20144, h20145, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h14396, h20086, h20089, h20144, hlam]
                      · linarith only [h16915, h18815, h20086, h20088, h20140, h20143, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h18815, h20087, h20138, h20140, h20141, h20142, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14396, h18815, h20086, h20140, h20141, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h18815, h20085, h20140, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h18815, h20000, h20088, hlam]
        · linarith only [h14396, h18815, h20087, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h20296 | h20296
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20297 | h20297
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20298 | h20298
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20299 | h20299
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20300 | h20300
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20301 | h20301
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20302 | h20302
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20303 | h20303
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20304 | h20304
                        · linarith only [h0, h18815, h18816, h20086, h20298, h20300, h20304, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h18815, h18816, h20300, h20301, h20304, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h16915, h18815, h20297, h20300, h20303, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h18815, h18816, h20086, h20300, h20301, h20302, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20309 | h20309
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20310 | h20310
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20311 | h20311
                        · linarith only [h20298, h20301, h20311, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20313 | h20313
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20314 | h20314
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20315 | h20315
                              · rcases h0bigk with h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c | h20316c
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h0, hlam, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h14396, hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h16915, hlam, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h0, h18816, h20298, h20301, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18816, h20298, hc01, hc13, hlam, hphi, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18816, hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h20000, hlam, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18815, h18816, h20298, h20300, h20301, h20313, h20315, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18815, h18816, h20298, h20300, h20301, h20313, h20315, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18816, h20298, h20301, hc02, hc34, hlam, hphi, ht23, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h20086, hlam, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  rcases p20316_3 (m.d 0 1) (by simp) with h20331 | h20331
                                  · linarith only [h14396, h20331, hlam]
                                  · linarith only [h18815, h20331, hlam]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18815, h20000, h20299, h20300, h20313, h20315, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h0, h18815, h20000, h20299, h20300, h20313, h20315, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h0, h18815, h18816, h20000, h20299, h20300, h20313, h20315, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  rcases p20316_3 (m.d 0 1) (by simp) with h20338 | h20338
                                  · linarith only [h16915, h20338, hlam]
                                  · linarith only [h18815, h20338, hlam]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h18815, hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h20085, hlam, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h20296, hlam, p20316_0]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [h20297, hlam, p20316_1]
                                · have p20316_0 := h20316c.1
                                  have p20316_1 := h20316c.2.1
                                  have p20316_2 := h20316c.2.2.1
                                  have p20316_3 := h20316c.2.2.2
                                  linarith only [hlam, p20316_0]
                              · linarith only [h14396, h20301, h20315, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h18815, h18816, h20310, h20311, h20314, hlam]
                          · linarith only [h0, h18815, h18816, h20296, h20300, h20313, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h18815, h18816, h20297, h20298, h20300, h20301, h20310, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h18815, h18816, h20296, h20298, h20300, h20309, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h16915, h20000, h20085, h20299, h20300, hlam]
              · linarith only [h18816, h20298, h20299, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20353 | h20353
              · linarith only [h0, h20000, h20298, h20353, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20355 | h20355
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20356 | h20356
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20357 | h20357
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20358 | h20358
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20359 | h20359
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20360 | h20360
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20361 | h20361
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20362 | h20362
                              · rcases h0bigk with h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c | h20363c
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h0, hlam, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h14396, hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h16915, hlam, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h0, h18815, h20353, h20355, h20360, h20362, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18816, h20086, h20356, hc01, hc14, hlam, hphi, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18816, hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h20000, hlam, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18815, h18816, h20086, h20298, h20355, h20356, h20360, h20362, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18815, h20086, h20298, h20355, h20356, h20360, h20362, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h20086, h20298, h20356, hc02, hc23, hlam, hphi, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h20086, hlam, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18815, h20086, h20298, h20355, h20356, h20360, h20362, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18815, h20086, h20298, h20355, h20356, h20360, h20362, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h0, h18815, h20086, h20298, h20355, h20356, h20360, h20362, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h14396, h18815, h20086, h20298, h20355, h20356, h20360, h20362, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  rcases p20363_3 (m.d 0 1) (by simp) with h20383 | h20383
                                  · linarith only [h16915, h20383, hlam]
                                  · linarith only [h18815, h20383, hlam]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h18815, hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h20085, hlam, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h20296, hlam, p20363_0]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [h20297, hlam, p20363_1]
                                · have p20363_0 := h20363c.1
                                  have p20363_1 := h20363c.2.1
                                  have p20363_2 := h20363c.2.2.1
                                  have p20363_3 := h20363c.2.2.2
                                  linarith only [hlam, p20363_0]
                              · linarith only [h0, h18815, h18816, h20086, h20297, h20362, hc04, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h18815, h20000, h20358, h20361, hlam]
                          · linarith only [h0, h18816, h20086, h20298, h20356, h20360, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h20298, h20356, h20359, hlam]
                      · linarith only [h16915, h20297, h20358, hlam]
                    · linarith only [h0, h18815, h18816, h20086, h20355, h20356, h20357, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20397 | h20397
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20398 | h20398
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20399 | h20399
                        · linarith only [h0, h18815, h20298, h20355, h20356, h20399, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h18815, h20298, h20355, h20399, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h16915, h20297, h20398, hlam]
                    · linarith only [h0, h18815, h20296, h20298, h20355, h20397, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h20085, h20355, hlam]
          · linarith only [h14396, h18815, h20086, h20297, hlam]
        · linarith only [h0, h18815, h18816, h20296, hlam]
    · linarith only [h0, h18815, h20085, hlam]

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  rcases m.htr 0 2 3 (by decide) (by decide) with h18816 | h18816
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  exact r1l7_10_12_23_L_I_L_I_H_I_s18 m hb0 hb2 hb3 h0 h14396 h16915 h18815

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  rcases m.htr 0 1 5 (by decide) (by decide) with h18815 | h18815
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h16920 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h16921 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h16922 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 1 2 3 (by decide) (by decide) with h16923 | h16923
  · rcases m.htr 1 2 4 (by decide) (by decide) with h16924 | h16924
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16925 | h16925
      · rcases m.htr 1 3 4 (by decide) (by decide) with h16926 | h16926
        · rcases m.htr 1 3 5 (by decide) (by decide) with h16927 | h16927
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16928 | h16928
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16929 | h16929
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16930 | h16930
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16931 | h16931
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16932 | h16932
                    · rcases h0bigk with h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c | h16933c
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h0, hlam, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h14396, hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h14396, h16915, h16924, h16929, h16932, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        rcases p16933_3 (m.d 0 1) (by simp) with h16938 | h16938
                        · rcases p16933_3 (m.d 0 2) (by simp) with h16939 | h16939
                          · rcases p16933_3 (m.d 0 3) (by simp) with h16940 | h16940
                            · rcases p16933_3 (m.d 0 4) (by simp) with h16941 | h16941
                              · linarith only [h16915, h16941, hlam]
                              · linarith only [h16922, h16941, hlam]
                            · linarith only [h16921, h16940, hlam]
                          · linarith only [h16919, h16939, hlam]
                        · linarith only [h16916, h16938, hlam]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h0, h16915, h16924, h16929, h16932, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h0, h14396, h16915, h16924, h16929, h16932, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        rcases p16933_3 (m.d 0 1) (by simp) with h16950 | h16950
                        · linarith only [h0, h16950, hlam]
                        · linarith only [h16915, h16950, hlam]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        rcases p16933_3 (m.d 0 1) (by simp) with h16953 | h16953
                        · linarith only [h0, h16953, hlam]
                        · linarith only [h16916, h16953, hlam]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16915, h16924, h16929, h16932, hc03, hc45, hlam, hphi, ht0b, ht5b, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16917, hlam, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        rcases p16933_3 (m.d 0 1) (by simp) with h16959 | h16959
                        · linarith only [h14396, h16959, hlam]
                        · linarith only [h16915, h16959, hlam]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        rcases p16933_3 (m.d 0 1) (by simp) with h16962 | h16962
                        · linarith only [h14396, h16962, hlam]
                        · linarith only [h16916, h16962, hlam]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16915, hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16918, hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16920, hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        rcases p16933_3 (m.d 0 1) (by simp) with h16969 | h16969
                        · rcases p16933_3 (m.d 0 2) (by simp) with h16970 | h16970
                          · rcases p16933_3 (m.d 0 3) (by simp) with h16971 | h16971
                            · rcases p16933_3 (m.d 0 4) (by simp) with h16972 | h16972
                              · rcases p16933_3 (m.d 0 5) (by simp) with h16973 | h16973
                                · linarith only [h16922, h16973, hlam]
                                · rcases h2bigk with h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c | h16975c
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h0, hlam, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h0, h16929, h16932, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    rcases p16975_3 (m.d 0 2) (by simp) with h16979 | h16979
                                    · rcases p16975_3 (m.d 1 2) (by simp) with h16980 | h16980
                                      · rcases p16975_3 (m.d 2 3) (by simp) with h16981 | h16981
                                        · linarith only [h16917, h16981, hlam]
                                        · linarith only [h16929, h16981, hlam]
                                      · linarith only [h16924, h16980, hlam]
                                    · linarith only [h16979, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    rcases p16975_3 (m.d 0 2) (by simp) with h16986 | h16986
                                    · rcases p16975_3 (m.d 1 2) (by simp) with h16987 | h16987
                                      · rcases p16975_3 (m.d 2 3) (by simp) with h16988 | h16988
                                        · linarith only [h16917, h16988, hlam]
                                        · linarith only [h16930, h16988, hlam]
                                      · linarith only [h16925, h16987, hlam]
                                    · linarith only [h16986, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h0, h16915, h16916, h16925, h16930, h16932, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16933_1, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16929, h16932, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    rcases p16975_3 (m.d 0 2) (by simp) with h16996 | h16996
                                    · linarith only [h0, h16996, hlam]
                                    · linarith only [h16918, h16996, hlam]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h0, h16915, h16916, h16925, hlam, p16933_1, p16975_2]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16917, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16923, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16917, h16929, h16932, hc02, hc45, hlam, hphi, ht0b, ht5b, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    rcases p16975_3 (m.d 0 2) (by simp) with h17004 | h17004
                                    · rcases p16975_3 (m.d 1 2) (by simp) with h17005 | h17005
                                      · rcases p16975_3 (m.d 2 3) (by simp) with h17006 | h17006
                                        · rcases p16975_3 (m.d 2 4) (by simp) with h17007 | h17007
                                          · linarith only [h16929, h17007, hlam]
                                          · linarith only [h16931, h17007, hlam]
                                        · linarith only [h16930, h17006, hlam]
                                      · linarith only [h16925, h17005, hlam]
                                    · linarith only [h16919, h17004, hlam]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16918, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16924, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16929, hlam, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h14396, h16915, h16924, h16930, h16932, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16919, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16925, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16930, hlam, p16975_1]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [h16931, hlam, p16975_0]
                                  · have p16975_0 := h16975c.1
                                    have p16975_1 := h16975c.2.1
                                    have p16975_2 := h16975c.2.2.1
                                    have p16975_3 := h16975c.2.2.2
                                    linarith only [hlam, p16975_0]
                              · linarith only [h16922, h16972, hlam]
                            · linarith only [h16921, h16971, hlam]
                          · linarith only [h16919, h16970, hlam]
                        · linarith only [h16916, h16969, hlam]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16916, hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16919, hlam, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16921, hlam, p16933_0]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [h16922, hlam, p16933_1]
                      · have p16933_0 := h16933c.1
                        have p16933_1 := h16933c.2.1
                        have p16933_2 := h16933c.2.2.1
                        have p16933_3 := h16933c.2.2.2
                        linarith only [hlam, p16933_0]
                    · linarith only [h14396, h16915, h16923, h16928, h16932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h14396, h16915, h16923, h16928, h16931, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h14396, h16915, h16923, h16927, h16928, h16929, h16930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h17035 | h17035
                · linarith only [h14396, h16915, h16923, h16926, h16929, h17035, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17037 | h17037
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17038 | h17038
                    · rcases h0bigk with h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c | h17039c
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h0, hlam, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h14396, hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h14396, h16915, h16923, h16927, h16928, h17035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h14396, h16916, h16923, h16927, h17035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h0, h16915, h16927, h16928, h17035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h0, h14396, h16915, h16927, h16928, h17035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        rcases p17039_3 (m.d 0 1) (by simp) with h17048 | h17048
                        · linarith only [h0, h17048, hlam]
                        · linarith only [h16915, h17048, hlam]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        rcases p17039_3 (m.d 0 1) (by simp) with h17051 | h17051
                        · linarith only [h0, h17051, hlam]
                        · linarith only [h16916, h17051, hlam]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16915, h16927, h16928, h17035, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16917, hlam, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        rcases p17039_3 (m.d 0 1) (by simp) with h17057 | h17057
                        · linarith only [h14396, h17057, hlam]
                        · linarith only [h16915, h17057, hlam]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        rcases p17039_3 (m.d 0 1) (by simp) with h17060 | h17060
                        · linarith only [h14396, h17060, hlam]
                        · linarith only [h16916, h17060, hlam]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16915, hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16918, hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16920, hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h0, h16915, h16916, h16927, h17035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16916, hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16919, hlam, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16921, hlam, p17039_0]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [h16922, hlam, p17039_1]
                      · have p17039_0 := h17039c.1
                        have p17039_1 := h17039c.2.1
                        have p17039_2 := h17039c.2.2.1
                        have p17039_3 := h17039c.2.2.2
                        linarith only [hlam, p17039_0]
                    · linarith only [h16929, h17037, h17038, hlam]
                  · linarith only [h14396, h16915, h16923, h16928, h17037, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h17075 | h17075
              · rcases m.htr 2 3 5 (by decide) (by decide) with h17076 | h17076
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17077 | h17077
                  · linarith only [h16924, h16928, h17077, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17079 | h17079
                    · linarith only [h16924, h16928, h17075, h17079, hlam]
                    · rcases h0bigk with h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c | h17081c
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h0, hlam, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h14396, hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h14396, h16922, h16923, h16928, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h14396, h16922, h16923, h16924, h16928, h17075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h0, h16915, h16922, h16924, h16928, h17075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h0, h14396, h16915, h16922, h16924, h16928, h17075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h0, h16922, h16924, h16928, h17075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        rcases p17081_3 (m.d 0 1) (by simp) with h17091 | h17091
                        · linarith only [h0, h17091, hlam]
                        · linarith only [h16916, h17091, hlam]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16915, h16922, h16924, h16928, h17075, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16917, hlam, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h14396, h16922, h16923, h16924, h16928, h17075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        rcases p17081_3 (m.d 0 1) (by simp) with h17098 | h17098
                        · linarith only [h14396, h17098, hlam]
                        · linarith only [h16916, h17098, hlam]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16915, hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16918, hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16920, hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h0, h16915, h16922, h16924, h16928, h17075, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16916, hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16919, hlam, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16921, hlam, p17081_0]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [h16922, hlam, p17081_1]
                      · have p17081_0 := h17081c.1
                        have p17081_1 := h17081c.2.1
                        have p17081_2 := h17081c.2.2.1
                        have p17081_3 := h17081c.2.2.2
                        linarith only [hlam, p17081_0]
                · linarith only [h14396, h16915, h16922, h16923, h16927, h16928, h17075, h17076, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h14396, h16915, h16922, h16923, h16926, h16928, h17075, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h14396, h16921, h16927, hlam]
        · linarith only [h14396, h16920, h16926, hlam]
      · linarith only [h0, h16919, h16925, hlam]
    · linarith only [h0, h16918, h16924, hlam]
  · linarith only [h0, h16917, h16923, hlam]

end R2N4
