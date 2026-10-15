import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S10
import Jsp000404.R1LeavesN7_4S14
import Jsp000404.R1LeavesN7_4S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6364 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6365 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6366 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h7114 | h7114
  · linarith only [h4, h6364, h6366, h7114, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7116 | h7116
    · linarith only [h0, h4, h6364, h7116, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7118 | h7118
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7119 | h7119
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7120 | h7120
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7121 | h7121
            · linarith only [h0, h1, h4, h6366, h7118, h7121, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h7116, h7119, h7121, hlam]
          · linarith only [h6365, h6366, h7116, h7118, h7120, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7125 | h7125
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7126 | h7126
            · linarith only [h1, h6366, h7126, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7128 | h7128
              · linarith only [h2, h7114, h7128, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7130 | h7130
                · rcases m.htr 2 3 5 (by decide) (by decide) with h7131 | h7131
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7132 | h7132
                    · linarith only [h0, h2, h4, h6366, h7114, h7118, h7131, h7132, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7134 | h7134
                      · linarith only [h4, h6364, h6366, h7130, h7131, h7132, h7134, hlam]
                      · rcases h1bigk with h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c | h7136c
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          rcases p7136_3 (m.d 0 1) (by simp) with h7138 | h7138
                          · rcases p7136_3 (m.d 1 2) (by simp) with h7139 | h7139
                            · linarith only [h7139, hlam, p7136_0]
                            · rcases p7136_3 (m.d 1 3) (by simp) with h7141 | h7141
                              · linarith only [h1, h7141, hlam]
                              · linarith only [h7116, h7141, hlam]
                          · linarith only [h7138, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          rcases p7136_3 (m.d 0 1) (by simp) with h7145 | h7145
                          · rcases p7136_3 (m.d 1 2) (by simp) with h7146 | h7146
                            · linarith only [h0, h7146, hlam]
                            · rcases p7136_3 (m.d 1 3) (by simp) with h7148 | h7148
                              · linarith only [h7148, hlam, p7136_0]
                              · rcases p7136_3 (m.d 1 4) (by simp) with h7150 | h7150
                                · linarith only [h2, h7150, hlam]
                                · rcases p7136_3 (m.d 1 5) (by simp) with h7152 | h7152
                                  · linarith only [h3, h7152, hlam]
                                  · linarith only [h7126, h7152, hlam]
                          · linarith only [h7145, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          rcases p7136_3 (m.d 0 1) (by simp) with h7156 | h7156
                          · rcases p7136_3 (m.d 1 2) (by simp) with h7157 | h7157
                            · linarith only [h0, h7157, hlam]
                            · linarith only [h7118, h7157, hlam]
                          · linarith only [h7156, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          rcases p7136_3 (m.d 0 1) (by simp) with h7161 | h7161
                          · rcases p7136_3 (m.d 1 2) (by simp) with h7162 | h7162
                            · linarith only [h0, h7162, hlam]
                            · rcases p7136_3 (m.d 1 3) (by simp) with h7164 | h7164
                              · linarith only [h1, h7164, hlam]
                              · rcases p7136_3 (m.d 1 4) (by simp) with h7166 | h7166
                                · linarith only [h2, h7166, hlam]
                                · rcases p7136_3 (m.d 1 5) (by simp) with h7168 | h7168
                                  · linarith only [h7168, hlam, p7136_0]
                                  · rcases h3bigk with h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c | h7170c
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h6366, h7131, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h4, hlam, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h6366, h7131, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h6366, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h1, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7116, hlam, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7126, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7116, h7118, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      rcases p7170_3 (m.d 0 3) (by simp) with h7184 | h7184
                                      · linarith only [h4, h7184, hlam]
                                      · linarith only [h6365, h7184, hlam]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h0, h4, h6366, h7118, h7130, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h6365, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7125, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7130, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7134, hlam, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h0, h4, h7118, h7130, h7131, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7116, h7118, h7130, h7131, h7132, hc34, hc45, hlam, hphi, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7131, hlam, p7170_0]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [h7131, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7170_1]
                                    · have p7170_0 := h7170c.1
                                      have p7170_1 := h7170c.2.1
                                      have p7170_2 := h7170c.2.2.1
                                      have p7170_3 := h7170c.2.2.2
                                      linarith only [hlam, p7170_0]
                          · linarith only [h7161, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h0, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h7116, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h0, h4, h6366, h7131, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h7119, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h1, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h1, h6366, h7131, hc12, hc23, hlam, hphi, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h1, h6366, h7118, h7130, h7131, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h7126, hlam, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h2, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h7118, hlam, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h7125, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h7128, hlam, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h3, hlam, p7136_0]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h3, h6366, h7118, h7130, h7131, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [h3, h6366, h7116, h7118, h7130, h7131, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7136_1]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          rcases p7136_3 (m.d 0 1) (by simp) with h7217 | h7217
                          · rcases p7136_3 (m.d 1 2) (by simp) with h7218 | h7218
                            · linarith only [h7119, h7218, hlam]
                            · linarith only [h7118, h7218, hlam]
                          · linarith only [h2, h7217, hlam]
                        · have p7136_0 := h7136c.1
                          have p7136_1 := h7136c.2.1
                          have p7136_2 := h7136c.2.2.1
                          have p7136_3 := h7136c.2.2.2
                          linarith only [hlam, p7136_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7223 | h7223
                    · linarith only [h0, h4, h7118, h7131, h7223, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7225 | h7225
                      · linarith only [h0, h4, h7118, h7130, h7131, h7223, h7225, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h4, h7118, h7130, h7131, h7225, hc34, hc45, hlam, hphi]
                · linarith only [h4, h6365, h7130, hlam]
          · linarith only [h6365, h6366, h7116, h7118, h7125, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
      · linarith only [h4, h6364, h7118, hc12, hc23, hlam, hphi]

set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6364 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6365 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h6366 | h6366
  · exact r1l7_11_23_L_I_H_I_s9_x0_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 h6364 h6365 h6366
  · exact r1l7_11_23_L_I_H_I_s9_x0_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 h6364 h6365 h6366

set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6364 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6365 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h4, h6364, h6365, hlam]

set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6364 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h6365 | h6365
  · exact r1l7_11_23_L_I_H_I_s9_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 h6364 h6365
  · exact r1l7_11_23_L_I_H_I_s9_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 h6364 h6365

set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  exact r1l7_11_23_L_I_H_I_s10 m hb1 hb3 h0 h1 h2 h3 h4 h6364

set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h6364 | h6364
  · exact r1l7_11_23_L_I_H_I_s9_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 h6364
  · exact r1l7_11_23_L_I_H_I_s9_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 h6364

set_option maxHeartbeats 20314000 in
set_option maxHeartbeats 20314000 in
theorem r1l7_11_23_L_I_H_I_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_23_L_I_H_I_s4 m hb1 hb3 h0 h1 h2 h3 h4
  · exact r1l7_11_23_L_I_H_I_s9 m hb1 hb3 h0 h1 h2 h3 h4

set_option maxHeartbeats 20562000 in
set_option maxHeartbeats 20562000 in
theorem r1l7_11_23_L_I_H_I_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_23_L_I_H_I_s3 m hb1 hb3 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h10161 | h10161
    · rcases m.htr 0 2 4 (by decide) (by decide) with h10162 | h10162
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10163 | h10163
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10164 | h10164
          · linarith only [h0, h10161, h10164, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10166 | h10166
            · linarith only [h0, h10161, h10163, h10166, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10168 | h10168
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10169 | h10169
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10170 | h10170
                  · linarith only [h0, h10170, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10172 | h10172
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10173 | h10173
                      · linarith only [h1, h10164, h10173, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h10168, h10173, h3, hc23, hc35, hlam, hphi]
                    · linarith only [h10163, h10164, h10172, hc13, hc35, hlam, hphi]
                · linarith only [h0, h10162, h10168, h10169, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10178 | h10178
                · linarith only [h0, h10161, h10168, h10178, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10180 | h10180
                  · linarith only [h0, h10161, h10168, h10180, h3, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h10161, h10168, h10180, h3, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10183 | h10183
          · linarith only [h1, h10183, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10185 | h10185
            · linarith only [h0, h10162, h10185, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10187 | h10187
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10188 | h10188
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10189 | h10189
                  · linarith only [h0, h10189, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10191 | h10191
                    · linarith only [h1, h10163, h10191, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10193 | h10193
                      · linarith only [h1, h10183, h10193, h3, hlam]
                      · linarith only [h0, h10187, h10193, h3, hc23, hc35, hlam, hphi]
                · linarith only [h0, h10162, h10187, h10188, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10197 | h10197
                · linarith only [h0, h10161, h10187, h10197, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10199 | h10199
                  · linarith only [h0, h10161, h10187, h10199, h3, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h10161, h10187, h10199, h3, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10202 | h10202
        · linarith only [h10161, h10162, h10202, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10204 | h10204
          · linarith only [h10161, h10162, h10204, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10206 | h10206
            · linarith only [h10206, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10208 | h10208
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10209 | h10209
                · linarith only [h0, h10162, h10209, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10211 | h10211
                  · linarith only [h10209, h10211, h2, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10213 | h10213
                    · linarith only [h1, h10202, h10211, h10213, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10215 | h10215
                      · linarith only [h1, h10204, h10215, h3, hlam]
                      · linarith only [h10208, h10209, h10215, h2, h3, hc23, hc35, hlam, hphi]
              · linarith only [h10161, h10162, h10208, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h10219 | h10219
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10220 | h10220
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10221 | h10221
          · linarith only [h1, h10221, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10223 | h10223
            · linarith only [h10223, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10225 | h10225
              · linarith only [h0, h10161, h10225, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10227 | h10227
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10228 | h10228
                  · linarith only [h1, h10225, h10228, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10230 | h10230
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10231 | h10231
                      · linarith only [h1, h10221, h10228, h10231, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h10233 | h10233
                        · linarith only [h1, h10161, h10219, h10223, h10225, h10233, h2, h3, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h10225, h10227, h10233, h3, hc24, hc45, hlam, hphi]
                    · linarith only [h1, h10220, h10225, h10227, h10230, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h10161, h10219, h10221, h10227, hc12, hc35, hlam, hphi, ht23]
        · linarith only [h10161, h10219, h10220, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10239 | h10239
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10240 | h10240
          · linarith only [h1, h10240, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10242 | h10242
            · linarith only [h1, h10239, h10242, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10244 | h10244
              · linarith only [h0, h10161, h10244, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10246 | h10246
                · linarith only [h0, h10219, h10246, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10248 | h10248
                  · linarith only [h1, h10244, h10248, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10250 | h10250
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10251 | h10251
                      · linarith only [h1, h10219, h10239, h10240, h10248, h10251, h3, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h10253 | h10253
                        · linarith only [h10242, h10253, h2, hlam]
                        · linarith only [h1, h10250, h10253, h3, hc34, hc45, hlam, hphi]
                    · linarith only [h10239, h10240, h10250, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10257 | h10257
          · linarith only [h1, h10257, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10259 | h10259
            · linarith only [h10259, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10261 | h10261
              · linarith only [h0, h10161, h10261, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10263 | h10263
                · linarith only [h1, h10219, h10239, h10261, h10263, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10265 | h10265
                  · linarith only [h0, h10265, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10267 | h10267
                    · linarith only [h0, h1, h10161, h10239, h10267, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10269 | h10269
                      · linarith only [h0, h1, h10239, h10257, h10269, h3, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h10271 | h10271
                        · linarith only [h10259, h10271, h2, h3, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h10273 | h10273
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h10274 | h10274
                            · linarith only [h10261, h10267, h10269, h10274, h2, h3, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h10161, h10239, h10273, h10274, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h10277 | h10277
                            · linarith only [h0, h10161, h10257, h10273, h10277, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h10279 | h10279
                              · linarith only [h10261, h10267, h10271, h10279, h2, h3, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h10281 | h10281
                                · linarith only [h0, h10161, h10273, h10279, h10281, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h10161, h10273, h10281, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 21150000 in
set_option maxHeartbeats 21150000 in
theorem r1l7_11_23_L_I_H_I_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_23_L_I_H_I_s2 m hb1 hb3 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h10284 | h10284
    · rcases m.htr 0 2 3 (by decide) (by decide) with h10285 | h10285
      · rcases m.htr 0 2 4 (by decide) (by decide) with h10286 | h10286
        · linarith only [h0, h10286, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h10288 | h10288
          · linarith only [h1, h10288, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h10290 | h10290
            · rcases m.htr 0 4 5 (by decide) (by decide) with h10291 | h10291
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10292 | h10292
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10293 | h10293
                  · linarith only [h0, h10286, h10293, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10295 | h10295
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10296 | h10296
                      · linarith only [h1, h10288, h10296, h2, hlam]
                      · linarith only [h0, h10292, h10296, h2, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10299 | h10299
                      · linarith only [h10284, h10288, h10290, h10292, h10295, h10299, hlam]
                      · linarith only [h10284, h10292, h10295, h10299, h2, hc23, hc34, hlam, hphi]
                · linarith only [h10285, h10286, h10292, hc12, hc24, hlam, hphi]
              · linarith only [h1, h10290, h10291, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h10304 | h10304
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10305 | h10305
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10306 | h10306
                  · linarith only [h0, h10286, h10306, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10308 | h10308
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10309 | h10309
                      · linarith only [h0, h10288, h10305, h10306, h10309, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h10305, h10309, h2, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10312 | h10312
                      · linarith only [h1, h10288, h10312, hlam]
                      · linarith only [h10284, h10305, h10308, h10312, h2, hc23, hc34, hlam, hphi]
                · linarith only [h10285, h10286, h10305, hc12, hc24, hlam, hphi]
              · linarith only [h10284, h10304, h2, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h10317 | h10317
        · linarith only [h1, h10285, h10317, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h10319 | h10319
          · linarith only [h1, h10319, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h10321 | h10321
            · rcases m.htr 0 4 5 (by decide) (by decide) with h10322 | h10322
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10323 | h10323
                · linarith only [h0, h10285, h10323, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10325 | h10325
                  · linarith only [h0, h10317, h10325, h2, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10327 | h10327
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10328 | h10328
                      · linarith only [h1, h10319, h10328, h2, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h10330 | h10330
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10331 | h10331
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h10332 | h10332
                            · linarith only [h1, h10323, h10327, h10328, h10332, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h10334 | h10334
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h10335 | h10335
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h10336 | h10336
                                  · rcases h1bigk with h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c | h10337c
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10325, h10327, h10332, h10334, h10336, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10323, h10325, h10327, h10332, h10334, h10336, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h2, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      rcases p10337_3 (m.d 0 1) (by simp) with h10342 | h10342
                                      · rcases p10337_3 (m.d 1 2) (by simp) with h10343 | h10343
                                        · linarith only [h0, h10343, hlam]
                                        · linarith only [h10327, h10343, hlam]
                                      · linarith only [h10342, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h0, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10323, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10325, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h0, h10325, h10332, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h1, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h1, h10325, h10332, h2, hc12, hc34, hlam, hphi, ht23, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10328, hlam, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h1, h10325, h10327, h10332, h10334, h10336, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h0, h10325, h10327, h10332, h10334, h10336, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      rcases p10337_3 (m.d 0 1) (by simp) with h10358 | h10358
                                      · linarith only [h10358, h2, hlam]
                                      · linarith only [h0, h10358, hlam]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      rcases p10337_3 (m.d 0 1) (by simp) with h10361 | h10361
                                      · linarith only [h10361, h2, hlam]
                                      · linarith only [h1, h10361, hlam]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      rcases p10337_3 (m.d 0 1) (by simp) with h10365 | h10365
                                      · linarith only [h10365, h2, hlam]
                                      · linarith only [h10284, h10365, hlam]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10284, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10327, hlam, p10337_1]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10330, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [h10331, hlam, p10337_0]
                                    · have p10337_0 := h10337c.1
                                      have p10337_1 := h10337c.2.1
                                      have p10337_2 := h10337c.2.2.1
                                      have p10337_3 := h10337c.2.2.2
                                      linarith only [hlam, p10337_0]
                                  · linarith only [h1, h10325, h10332, h10336, h2, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h1, h10323, h10325, h10327, h10331, h10334, h10335, h2, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1, h10321, h10325, h10332, h10334, h2, hc23, hc34, hlam, hphi]
                          · linarith only [h1, h10323, h10331, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h10321, h10323, h10327, h10330, h2, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10378 | h10378
                      · linarith only [h1, h10285, h10319, h10378, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h10380 | h10380
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10381 | h10381
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h10382 | h10382
                            · linarith only [h0, h10378, h10382, h2, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h10384 | h10384
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h10385 | h10385
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h10386 | h10386
                                  · rcases h1bigk with h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c | h10387c
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10325, h10382, h2, hc12, hc34, hlam, hphi, ht23, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10380, h10386, h2, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h2, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10325, h10327, h10382, h2, hc12, hc34, hlam, hphi, ht23, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h0, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10323, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10325, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10327, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h1, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10378, hlam, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h1, h10325, h10327, h10382, h2, hc12, hc34, hlam, hphi, ht23, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h1, h10325, h10382, hc13, hc34, hlam, hphi, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      rcases p10387_3 (m.d 0 1) (by simp) with h10404 | h10404
                                      · linarith only [h10404, h2, hlam]
                                      · linarith only [h0, h10404, hlam]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      rcases p10387_3 (m.d 0 1) (by simp) with h10407 | h10407
                                      · linarith only [h10407, h2, hlam]
                                      · linarith only [h1, h10407, hlam]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      rcases p10387_3 (m.d 0 1) (by simp) with h10411 | h10411
                                      · linarith only [h10411, h2, hlam]
                                      · linarith only [h10284, h10411, hlam]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10284, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10284, h10325, h10382, h2, hc12, hc34, hlam, hphi, ht23, p10387_1]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10380, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [h10381, hlam, p10387_0]
                                    · have p10387_0 := h10387c.1
                                      have p10387_1 := h10387c.2.1
                                      have p10387_2 := h10387c.2.2.1
                                      have p10387_3 := h10387c.2.2.2
                                      linarith only [hlam, p10387_0]
                                  · linarith only [h1, h10325, h10382, h10386, h2, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h1, h10325, h10380, h10381, h10385, h2, hlam]
                              · linarith only [h1, h10380, h10384, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1, h10327, h10380, h10381, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h10321, h10378, h10380, h2, hc13, hc34, hlam, hphi]
              · linarith only [h10284, h10322, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h10425 | h10425
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10426 | h10426
                · linarith only [h0, h10285, h10426, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10428 | h10428
                  · linarith only [h0, h10317, h10428, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10430 | h10430
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10431 | h10431
                      · linarith only [h0, h1, h10319, h10321, h10431, h2, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h10433 | h10433
                        · linarith only [h1, h10321, h10433, hlam]
                        · linarith only [h10426, h10430, h10433, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10436 | h10436
                      · linarith only [h1, h10285, h10319, h10436, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h10438 | h10438
                        · linarith only [h1, h10321, h10438, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10440 | h10440
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h10441 | h10441
                            · linarith only [h0, h10436, h10441, h2, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h10443 | h10443
                              · linarith only [h0, h10285, h10321, h10441, h10443, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h10445 | h10445
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h10446 | h10446
                                  · rcases h1bigk with h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c | h10447c
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10428, h10441, h2, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10426, h10428, h10441, h2, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h2, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10428, h10430, h10441, h2, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h0, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10426, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10428, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10430, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h1, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h1, h10428, h10441, h2, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10436, hlam, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10438, hlam, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h0, h10428, h10441, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      rcases p10447_3 (m.d 0 1) (by simp) with h10464 | h10464
                                      · linarith only [h10464, h2, hlam]
                                      · linarith only [h0, h10464, hlam]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      rcases p10447_3 (m.d 0 1) (by simp) with h10467 | h10467
                                      · linarith only [h10467, h2, hlam]
                                      · linarith only [h1, h10467, hlam]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      rcases p10447_3 (m.d 0 1) (by simp) with h10471 | h10471
                                      · linarith only [h10471, h2, hlam]
                                      · linarith only [h10284, h10471, hlam]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10284, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10284, h10428, h10441, h2, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10284, h10426, h10428, h10441, h2, hc12, hc34, hlam, hphi, ht23, p10447_1]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [h10440, hlam, p10447_0]
                                    · have p10447_0 := h10447c.1
                                      have p10447_1 := h10447c.2.1
                                      have p10447_2 := h10447c.2.2.1
                                      have p10447_3 := h10447c.2.2.2
                                      linarith only [hlam, p10447_0]
                                  · linarith only [h0, h10428, h10441, h10446, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h10284, h10428, h10440, h10445, h2, hlam]
                          · linarith only [h10284, h10426, h10438, h10440, h2, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h10284, h10425, h2, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h10483 | h10483
      · rcases m.htr 0 2 4 (by decide) (by decide) with h10484 | h10484
        · linarith only [h0, h10484, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h10486 | h10486
          · linarith only [h1, h10486, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h10488 | h10488
            · linarith only [h0, h10284, h10483, h10488, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h10490 | h10490
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10491 | h10491
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10492 | h10492
                  · linarith only [h0, h10484, h10492, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10494 | h10494
                    · linarith only [h0, h10284, h10494, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10496 | h10496
                      · linarith only [h1, h10284, h10486, h10490, h10496, hlam]
                      · linarith only [h0, h10491, h10496, h2, hc23, hc34, hlam, hphi]
                · linarith only [h10483, h10484, h10491, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10500 | h10500
                · linarith only [h0, h10490, h10500, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h10483, h10490, h10500, h2, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h10503 | h10503
        · linarith only [h0, h10503, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h10505 | h10505
          · linarith only [h1, h10505, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h10507 | h10507
            · linarith only [h1, h10284, h10507, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h10509 | h10509
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10510 | h10510
                · linarith only [h0, h10483, h10510, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10512 | h10512
                  · linarith only [h0, h10284, h10503, h10509, h10512, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10514 | h10514
                    · linarith only [h1, h10284, h10510, h10514, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10516 | h10516
                      · linarith only [h1, h10483, h10505, h10512, h10516, h2, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h10518 | h10518
                        · linarith only [h1, h10284, h10507, h10518, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10520 | h10520
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h10521 | h10521
                            · linarith only [h0, h10284, h10516, h10520, h10521, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h10523 | h10523
                              · linarith only [h1, h10284, h10510, h10518, h10521, h10523, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h10525 | h10525
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h10526 | h10526
                                  · rcases h1bigk with h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c | h10527c
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10284, h10512, h10520, hc12, hc24, hlam, hphi, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10284, h10510, h10512, h10520, hc12, hc24, hlam, hphi, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h2, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10284, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h0, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10510, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10512, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10514, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h1, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h1, h10284, h10512, h10520, hc12, hc24, hlam, hphi, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10516, hlam, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10518, hlam, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h0, h10512, hc12, hc24, hlam, hphi, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      rcases p10527_3 (m.d 0 1) (by simp) with h10544 | h10544
                                      · linarith only [h10544, h2, hlam]
                                      · linarith only [h0, h10544, hlam]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      rcases p10527_3 (m.d 0 1) (by simp) with h10547 | h10547
                                      · linarith only [h10547, h2, hlam]
                                      · linarith only [h1, h10547, hlam]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h1, h10284, h10510, h10512, h10521, hc12, hc34, hlam, hphi, ht23, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h1, h10510, h10514, hc12, hc25, hlam, hphi, p10527_1]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      rcases p10527_3 (m.d 0 1) (by simp) with h10553 | h10553
                                      · linarith only [h10284, h10553, hlam]
                                      · linarith only [h0, h10553, hlam]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      rcases p10527_3 (m.d 0 1) (by simp) with h10556 | h10556
                                      · linarith only [h10284, h10556, hlam]
                                      · linarith only [h1, h10556, hlam]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [h10520, hlam, p10527_0]
                                    · have p10527_0 := h10527c.1
                                      have p10527_1 := h10527c.2.1
                                      have p10527_2 := h10527c.2.2.1
                                      have p10527_3 := h10527c.2.2.2
                                      linarith only [hlam, p10527_0]
                                  · linarith only [h1, h10509, h10510, h10512, h10521, h10526, h2, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h10509, h10512, h10525, h2, hlam]
                          · linarith only [h10509, h10520, h2, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10564 | h10564
                · linarith only [h0, h10483, h10564, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10566 | h10566
                  · linarith only [h0, h10509, h10566, h2, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10568 | h10568
                    · linarith only [h0, h10284, h10568, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10570 | h10570
                      · linarith only [h1, h10505, h10509, h10570, h2, hc03, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h10572 | h10572
                        · linarith only [h1, h10507, h10509, h10572, h2, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10574 | h10574
                          · linarith only [h1, h10509, h10570, h10574, h2, hc13, hc34, hlam, hphi]
                          · linarith only [h1, h10564, h10574, h2, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
