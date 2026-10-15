import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S28

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 0 4 5 (by decide) (by decide) with h21036 | h21036
  · linarith only [h19113, h19114, h21036, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h21038 | h21038
    · rcases m.htr 1 2 4 (by decide) (by decide) with h21039 | h21039
      · rcases m.htr 1 2 5 (by decide) (by decide) with h21040 | h21040
        · rcases m.htr 1 3 4 (by decide) (by decide) with h21041 | h21041
          · rcases m.htr 1 3 5 (by decide) (by decide) with h21042 | h21042
            · rcases m.htr 1 4 5 (by decide) (by decide) with h21043 | h21043
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21044 | h21044
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21045 | h21045
                  · linarith only [h19110, h19114, h21045, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h21047 | h21047
                    · linarith only [h19111, h21036, h21047, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21049 | h21049
                      · linarith only [h19110, h19114, h21036, h21038, h21042, h21044, h21049, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c | h21051c
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h0, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h14799, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h16563, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h17994, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          rcases p21051_3 (m.d 0 1) (by simp) with h21057 | h21057
                          · linarith only [h21057, hlam, p21051_0]
                          · rcases p21051_3 (m.d 1 2) (by simp) with h21059 | h21059
                            · rcases p21051_3 (m.d 1 3) (by simp) with h21060 | h21060
                              · linarith only [h21038, h21060, hlam]
                              · linarith only [h14799, h21060, hlam]
                            · linarith only [h21059, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h19114, h21041, h21043, h21049, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h19110, h19114, h21043, h21044, h21049, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h19110, h19114, h21043, h21044, h21049, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          rcases p21051_3 (m.d 0 1) (by simp) with h21068 | h21068
                          · linarith only [h21068, hlam, p21051_0]
                          · rcases p21051_3 (m.d 1 2) (by simp) with h21070 | h21070
                            · rcases p21051_3 (m.d 1 3) (by simp) with h21071 | h21071
                              · rcases p21051_3 (m.d 1 4) (by simp) with h21072 | h21072
                                · linarith only [h21041, h21072, hlam]
                                · linarith only [h16563, h21072, hlam]
                              · linarith only [h21071, hlam, p21051_0]
                            · linarith only [h0, h21070, hlam]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h21038, hlam, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h19110, h19114, h21043, h21044, h21049, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h19110, h19114, h21038, h21043, h21044, h21049, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          rcases p21051_3 (m.d 0 1) (by simp) with h21081 | h21081
                          · linarith only [h21081, hlam, p21051_0]
                          · rcases p21051_3 (m.d 1 2) (by simp) with h21083 | h21083
                            · rcases p21051_3 (m.d 1 3) (by simp) with h21084 | h21084
                              · rcases p21051_3 (m.d 1 4) (by simp) with h21085 | h21085
                                · rcases p21051_3 (m.d 1 5) (by simp) with h21086 | h21086
                                  · linarith only [h21043, h21086, hlam]
                                  · linarith only [h17994, h21086, hlam]
                                · linarith only [h21085, hlam, p21051_0]
                              · linarith only [h14799, h21084, hlam]
                            · linarith only [h0, h21083, hlam]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h21039, hlam, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h21041, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h19110, h19114, h21043, h21044, h21049, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          rcases p21051_3 (m.d 0 1) (by simp) with h21096 | h21096
                          · linarith only [h21096, hlam, p21051_0]
                          · rcases p21051_3 (m.d 1 2) (by simp) with h21098 | h21098
                            · rcases p21051_3 (m.d 1 3) (by simp) with h21099 | h21099
                              · rcases p21051_3 (m.d 1 4) (by simp) with h21100 | h21100
                                · rcases p21051_3 (m.d 1 5) (by simp) with h21101 | h21101
                                  · rcases h3bigk with h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c | h21102c
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h14799, hlam, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19114, h21044, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19114, h21049, hc34, hc45, hlam, hphi, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19114, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      rcases p21102_3 (m.d 0 3) (by simp) with h21108 | h21108
                                      · linarith only [h14799, h21108, hlam]
                                      · rcases p21102_3 (m.d 1 3) (by simp) with h21110 | h21110
                                        · rcases p21102_3 (m.d 2 3) (by simp) with h21111 | h21111
                                          · linarith only [h21038, h21111, hlam]
                                          · rcases p21102_3 (m.d 3 4) (by simp) with h21113 | h21113
                                            · linarith only [h21041, h21113, hlam]
                                            · rcases p21102_3 (m.d 3 5) (by simp) with h21115 | h21115
                                              · linarith only [h21042, h21115, hlam]
                                              · linarith only [h19114, h21115, hlam]
                                        · linarith only [h14799, h21110, hlam]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      rcases p21102_3 (m.d 0 3) (by simp) with h21120 | h21120
                                      · linarith only [h14799, h21120, hlam]
                                      · linarith only [h19110, h21120, hlam]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19110, h19114, h21041, h21043, h21044, h21049, hlam, p21102_2]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19110, h19114, h21038, h21044, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19110, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21038, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19110, h19114, h21049, hc34, hc45, hlam, hphi, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21045, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19113, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21041, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21044, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21049, hlam, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h19113, h21049, hc34, hc45, hlam, hphi, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21042, hlam, p21102_0]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [h21038, h21042, h21044, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21102_1]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      rcases p21102_3 (m.d 0 3) (by simp) with h21138 | h21138
                                      · linarith only [h19114, h21138, hlam]
                                      · linarith only [h19113, h21138, hlam]
                                    · have p21102_0 := h21102c.1
                                      have p21102_1 := h21102c.2.1
                                      have p21102_2 := h21102c.2.2.1
                                      have p21102_3 := h21102c.2.2.2
                                      linarith only [hlam, p21102_0]
                                  · linarith only [h21101, hlam, p21051_0]
                                · linarith only [h16563, h21100, hlam]
                              · linarith only [h14799, h21099, hlam]
                            · linarith only [h0, h21098, hlam]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h21040, hlam, p21051_1]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h21042, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [h21043, hlam, p21051_0]
                        · have p21051_0 := h21051c.1
                          have p21051_1 := h21051c.2.1
                          have p21051_2 := h21051c.2.2.1
                          have p21051_3 := h21051c.2.2.2
                          linarith only [hlam, p21051_0]
                · linarith only [h19113, h19114, h21044, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21151 | h21151
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21152 | h21152
                  · linarith only [h19110, h19114, h21152, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h21154 | h21154
                    · linarith only [h16563, h21043, h21154, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21156 | h21156
                      · linarith only [h19110, h19114, h21038, h21042, h21043, h21151, h21156, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c | h21158c
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h0, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h14799, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h16563, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h17994, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          rcases p21158_3 (m.d 0 1) (by simp) with h21164 | h21164
                          · linarith only [h21164, hlam, p21158_0]
                          · rcases p21158_3 (m.d 1 2) (by simp) with h21166 | h21166
                            · rcases p21158_3 (m.d 1 3) (by simp) with h21167 | h21167
                              · linarith only [h21038, h21167, hlam]
                              · linarith only [h14799, h21167, hlam]
                            · linarith only [h21166, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h19114, h21042, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h16563, hc01, hc12, hlam, hphi, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h17994, hc01, hc12, hlam, hphi, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          rcases p21158_3 (m.d 0 1) (by simp) with h21175 | h21175
                          · linarith only [h21175, hlam, p21158_0]
                          · rcases p21158_3 (m.d 1 2) (by simp) with h21177 | h21177
                            · rcases p21158_3 (m.d 1 3) (by simp) with h21178 | h21178
                              · rcases p21158_3 (m.d 1 4) (by simp) with h21179 | h21179
                                · linarith only [h21041, h21179, hlam]
                                · linarith only [h16563, h21179, hlam]
                              · linarith only [h21178, hlam, p21158_0]
                            · linarith only [h0, h21177, hlam]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21038, hlam, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h16563, hc01, hc13, hlam, hphi, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h19110, h19114, h21038, h21042, h21151, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21043, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21039, hlam, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21041, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21043, hlam, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          rcases p21158_3 (m.d 0 1) (by simp) with h21193 | h21193
                          · linarith only [h21193, hlam, p21158_0]
                          · rcases p21158_3 (m.d 1 2) (by simp) with h21195 | h21195
                            · rcases p21158_3 (m.d 1 3) (by simp) with h21196 | h21196
                              · rcases p21158_3 (m.d 1 4) (by simp) with h21197 | h21197
                                · linarith only [h21043, h21197, hlam]
                                · linarith only [h16563, h21197, hlam]
                              · linarith only [h14799, h21196, hlam]
                            · linarith only [h0, h21195, hlam]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21040, hlam, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h21042, hlam, p21158_0]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [h16563, hc01, hc15, hlam, hphi, p21158_1]
                        · have p21158_0 := h21158c.1
                          have p21158_1 := h21158c.2.1
                          have p21158_2 := h21158c.2.2.1
                          have p21158_3 := h21158c.2.2.2
                          linarith only [hlam, p21158_0]
                · linarith only [h19113, h19114, h21151, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h21207 | h21207
              · linarith only [h16563, h21036, h21041, h21042, h21207, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21209 | h21209
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21210 | h21210
                  · linarith only [h14799, h19110, h21042, h21210, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h21212 | h21212
                    · linarith only [h0, h17994, h19111, h21207, h21212, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h21214 | h21214
                      · linarith only [h16563, h19110, h21207, h21209, h21214, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c | h21216c
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h0, hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h14799, hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h16563, hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h17994, hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          rcases p21216_3 (m.d 0 1) (by simp) with h21222 | h21222
                          · linarith only [h21222, hlam, p21216_0]
                          · rcases p21216_3 (m.d 1 2) (by simp) with h21224 | h21224
                            · rcases p21216_3 (m.d 1 3) (by simp) with h21225 | h21225
                              · linarith only [h21038, h21225, hlam]
                              · linarith only [h14799, h21225, hlam]
                            · linarith only [h21224, hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h14799, hc01, hc12, hlam, hphi, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h16563, hc01, hc12, hlam, hphi, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h17994, hc01, hc12, hlam, hphi, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21042, hc01, hc35, hlam, hphi, ht12, ht23, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21038, hlam, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h16563, h21042, h21214, hc04, hc45, hlam, hphi, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21042, hlam, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21041, h21042, h21214, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21039, hlam, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21041, hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [hlam, p21216_0]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21207, hlam, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          rcases p21216_3 (m.d 0 1) (by simp) with h21243 | h21243
                          · linarith only [h21243, hlam, p21216_0]
                          · rcases p21216_3 (m.d 1 2) (by simp) with h21245 | h21245
                            · rcases p21216_3 (m.d 1 3) (by simp) with h21246 | h21246
                              · linarith only [h21042, h21246, hlam]
                              · linarith only [h14799, h21246, hlam]
                            · linarith only [h0, h21245, hlam]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h21040, hlam, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h14799, hc01, hc15, hlam, hphi, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [h16563, hc01, hc15, hlam, hphi, p21216_1]
                        · have p21216_0 := h21216c.1
                          have p21216_1 := h21216c.2.1
                          have p21216_2 := h21216c.2.2.1
                          have p21216_3 := h21216c.2.2.2
                          linarith only [hlam, p21216_0]
                · linarith only [h19113, h19114, h21209, hc23, hc35, hlam, hphi]
          · linarith only [h14799, h19113, h21041, hlam]
        · linarith only [h0, h19112, h21040, hlam]
      · linarith only [h0, h19111, h21039, hlam]
    · linarith only [h0, h19110, h21038, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 0 3 5 (by decide) (by decide) with h19114 | h19114
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114

end R2N4
