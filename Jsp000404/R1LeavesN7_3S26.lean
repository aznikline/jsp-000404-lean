import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h19120 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h19121 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h19122 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h19123 | h19123
  · rcases m.htr 2 4 5 (by decide) (by decide) with h19124 | h19124
    · rcases m.htr 3 4 5 (by decide) (by decide) with h19125 | h19125
      · rcases h1bigk with h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c | h19126c
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h0, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h14799, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h16563, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h17994, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          rcases p19126_3 (m.d 0 1) (by simp) with h19132 | h19132
          · linarith only [h19132, hlam, p19126_0]
          · rcases p19126_3 (m.d 1 2) (by simp) with h19134 | h19134
            · rcases p19126_3 (m.d 1 3) (by simp) with h19135 | h19135
              · linarith only [h19116, h19135, hlam]
              · linarith only [h14799, h19135, hlam]
            · linarith only [h19134, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h14799, hc01, hc12, hlam, hphi, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h16563, hc01, hc12, hlam, hphi, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          rcases p19126_3 (m.d 0 1) (by simp) with h19143 | h19143
          · linarith only [h19143, hlam, p19126_0]
          · rcases p19126_3 (m.d 1 2) (by simp) with h19145 | h19145
            · rcases p19126_3 (m.d 1 3) (by simp) with h19146 | h19146
              · rcases p19126_3 (m.d 1 4) (by simp) with h19147 | h19147
                · linarith only [h19119, h19147, hlam]
                · linarith only [h16563, h19147, hlam]
              · linarith only [h19146, hlam, p19126_0]
            · linarith only [h0, h19145, hlam]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h19116, hlam, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h17994, h19121, hc01, hc13, hlam, hphi, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h17994, h19116, hc01, hc12, hlam, hphi, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          rcases p19126_3 (m.d 0 1) (by simp) with h19156 | h19156
          · linarith only [h19156, hlam, p19126_0]
          · rcases p19126_3 (m.d 1 2) (by simp) with h19158 | h19158
            · rcases p19126_3 (m.d 1 3) (by simp) with h19159 | h19159
              · rcases p19126_3 (m.d 1 4) (by simp) with h19160 | h19160
                · rcases p19126_3 (m.d 1 5) (by simp) with h19161 | h19161
                  · linarith only [h19121, h19161, hlam]
                  · linarith only [h17994, h19161, hlam]
                · linarith only [h19160, hlam, p19126_0]
              · linarith only [h14799, h19159, hlam]
            · linarith only [h0, h19158, hlam]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h19117, hlam, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h19119, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h17994, hc01, hc14, hlam, hphi, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          rcases p19126_3 (m.d 0 1) (by simp) with h19171 | h19171
          · linarith only [h19171, hlam, p19126_0]
          · rcases p19126_3 (m.d 1 2) (by simp) with h19173 | h19173
            · rcases p19126_3 (m.d 1 3) (by simp) with h19174 | h19174
              · rcases p19126_3 (m.d 1 4) (by simp) with h19175 | h19175
                · rcases p19126_3 (m.d 1 5) (by simp) with h19176 | h19176
                  · rcases h3bigk with h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c | h19177c
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h14799, hlam, p19177_1]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19122, h19125, hc03, hc45, hlam, hphi, ht0b, ht5b, p19177_1]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      rcases p19177_3 (m.d 0 3) (by simp) with h19181 | h19181
                      · rcases p19177_3 (m.d 1 3) (by simp) with h19182 | h19182
                        · rcases p19177_3 (m.d 2 3) (by simp) with h19183 | h19183
                          · linarith only [h19110, h19183, hlam]
                          · linarith only [h19122, h19183, hlam]
                        · linarith only [h19119, h19182, hlam]
                      · linarith only [h19181, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      rcases p19177_3 (m.d 0 3) (by simp) with h19188 | h19188
                      · rcases p19177_3 (m.d 1 3) (by simp) with h19189 | h19189
                        · rcases p19177_3 (m.d 2 3) (by simp) with h19190 | h19190
                          · linarith only [h19110, h19190, hlam]
                          · linarith only [h19123, h19190, hlam]
                        · linarith only [h19120, h19189, hlam]
                      · linarith only [h19188, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19110, h19116, h19122, h19125, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19177_1]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19116, h19122, h19125, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19177_1]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      rcases p19177_3 (m.d 0 3) (by simp) with h19198 | h19198
                      · linarith only [h14799, h19198, hlam]
                      · linarith only [h19113, h19198, hlam]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      rcases p19177_3 (m.d 0 3) (by simp) with h19201 | h19201
                      · linarith only [h14799, h19201, hlam]
                      · linarith only [h19114, h19201, hlam]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19110, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19116, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19110, h19125, hc02, hc45, hlam, hphi, ht0b, ht5b, p19177_1]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      rcases p19177_3 (m.d 0 3) (by simp) with h19208 | h19208
                      · rcases p19177_3 (m.d 1 3) (by simp) with h19209 | h19209
                        · rcases p19177_3 (m.d 2 3) (by simp) with h19210 | h19210
                          · rcases p19177_3 (m.d 3 4) (by simp) with h19211 | h19211
                            · linarith only [h19122, h19211, hlam]
                            · linarith only [h19125, h19211, hlam]
                          · linarith only [h19210, hlam, p19177_0]
                        · linarith only [h19120, h19209, hlam]
                      · linarith only [h19114, h19208, hlam]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19113, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19119, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19122, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h0, h19110, h19122, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19177_1]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19114, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19120, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19123, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [h19125, hlam, p19177_0]
                    · have p19177_0 := h19177c.1
                      have p19177_1 := h19177c.2.1
                      have p19177_2 := h19177c.2.2.1
                      have p19177_3 := h19177c.2.2.2
                      linarith only [hlam, p19177_0]
                  · linarith only [h19176, hlam, p19126_0]
                · linarith only [h16563, h19175, hlam]
              · linarith only [h14799, h19174, hlam]
            · linarith only [h0, h19173, hlam]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h19118, hlam, p19126_1]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h19120, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [h19121, hlam, p19126_0]
        · have p19126_0 := h19126c.1
          have p19126_1 := h19126c.2.1
          have p19126_2 := h19126c.2.2.1
          have p19126_3 := h19126c.2.2.2
          linarith only [hlam, p19126_0]
      · rcases h1bigk with h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c | h19235c
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h0, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h14799, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h16563, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h17994, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          rcases p19235_3 (m.d 0 1) (by simp) with h19241 | h19241
          · linarith only [h19241, hlam, p19235_0]
          · rcases p19235_3 (m.d 1 2) (by simp) with h19243 | h19243
            · rcases p19235_3 (m.d 1 3) (by simp) with h19244 | h19244
              · linarith only [h19116, h19244, hlam]
              · linarith only [h14799, h19244, hlam]
            · linarith only [h19243, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h14799, hc01, hc12, hlam, hphi, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h16563, h19115, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          rcases p19235_3 (m.d 0 1) (by simp) with h19252 | h19252
          · linarith only [h19252, hlam, p19235_0]
          · rcases p19235_3 (m.d 1 2) (by simp) with h19254 | h19254
            · rcases p19235_3 (m.d 1 3) (by simp) with h19255 | h19255
              · rcases p19235_3 (m.d 1 4) (by simp) with h19256 | h19256
                · linarith only [h19119, h19256, hlam]
                · linarith only [h16563, h19256, hlam]
              · linarith only [h19255, hlam, p19235_0]
            · linarith only [h0, h19254, hlam]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h19116, hlam, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h16563, h19111, h19124, h19125, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h17994, h19116, hc01, hc12, hlam, hphi, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          rcases p19235_3 (m.d 0 1) (by simp) with h19265 | h19265
          · linarith only [h19265, hlam, p19235_0]
          · rcases p19235_3 (m.d 1 2) (by simp) with h19267 | h19267
            · rcases p19235_3 (m.d 1 3) (by simp) with h19268 | h19268
              · rcases p19235_3 (m.d 1 4) (by simp) with h19269 | h19269
                · rcases p19235_3 (m.d 1 5) (by simp) with h19270 | h19270
                  · linarith only [h19121, h19270, hlam]
                  · linarith only [h17994, h19270, hlam]
                · linarith only [h19269, hlam, p19235_0]
              · linarith only [h14799, h19268, hlam]
            · linarith only [h0, h19267, hlam]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h19117, hlam, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h19119, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h17994, hc01, hc14, hlam, hphi, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          rcases p19235_3 (m.d 0 1) (by simp) with h19280 | h19280
          · linarith only [h19280, hlam, p19235_0]
          · rcases p19235_3 (m.d 1 2) (by simp) with h19282 | h19282
            · rcases p19235_3 (m.d 1 3) (by simp) with h19283 | h19283
              · rcases p19235_3 (m.d 1 4) (by simp) with h19284 | h19284
                · rcases p19235_3 (m.d 1 5) (by simp) with h19285 | h19285
                  · rcases h3bigk with h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c | h19286c
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h14799, hlam, p19286_1]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h0, h19110, h19122, h19124, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19286_1]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      rcases p19286_3 (m.d 0 3) (by simp) with h19290 | h19290
                      · rcases p19286_3 (m.d 1 3) (by simp) with h19291 | h19291
                        · rcases p19286_3 (m.d 2 3) (by simp) with h19292 | h19292
                          · linarith only [h19110, h19292, hlam]
                          · linarith only [h19122, h19292, hlam]
                        · linarith only [h19119, h19291, hlam]
                      · linarith only [h19290, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      rcases p19286_3 (m.d 0 3) (by simp) with h19297 | h19297
                      · rcases p19286_3 (m.d 1 3) (by simp) with h19298 | h19298
                        · rcases p19286_3 (m.d 2 3) (by simp) with h19299 | h19299
                          · linarith only [h19110, h19299, hlam]
                          · linarith only [h19123, h19299, hlam]
                        · linarith only [h19120, h19298, hlam]
                      · linarith only [h19297, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19110, h19116, h19122, h19124, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19286_1]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19116, h19122, h19124, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19286_1]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      rcases p19286_3 (m.d 0 3) (by simp) with h19307 | h19307
                      · linarith only [h14799, h19307, hlam]
                      · linarith only [h19113, h19307, hlam]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      rcases p19286_3 (m.d 0 3) (by simp) with h19310 | h19310
                      · linarith only [h14799, h19310, hlam]
                      · linarith only [h19114, h19310, hlam]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19110, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19116, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      rcases p19286_3 (m.d 0 3) (by simp) with h19316 | h19316
                      · rcases p19286_3 (m.d 1 3) (by simp) with h19317 | h19317
                        · rcases p19286_3 (m.d 2 3) (by simp) with h19318 | h19318
                          · rcases p19286_3 (m.d 3 4) (by simp) with h19319 | h19319
                            · linarith only [h19319, hlam, p19286_0]
                            · rcases p19286_3 (m.d 3 5) (by simp) with h19321 | h19321
                              · linarith only [h19123, h19321, hlam]
                              · linarith only [h19125, h19321, hlam]
                          · linarith only [h19318, hlam, p19286_0]
                        · linarith only [h19119, h19317, hlam]
                      · linarith only [h19113, h19316, hlam]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      rcases p19286_3 (m.d 0 3) (by simp) with h19327 | h19327
                      · rcases p19286_3 (m.d 1 3) (by simp) with h19328 | h19328
                        · rcases p19286_3 (m.d 2 3) (by simp) with h19329 | h19329
                          · rcases p19286_3 (m.d 3 4) (by simp) with h19330 | h19330
                            · linarith only [h19122, h19330, hlam]
                            · rcases p19286_3 (m.d 3 5) (by simp) with h19332 | h19332
                              · linarith only [h19332, hlam, p19286_0]
                              · rcases h5bigk with h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c | h19334c
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h17994, hlam, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19124, h19125, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  rcases p19334_3 (m.d 0 5) (by simp) with h19338 | h19338
                                  · rcases p19334_3 (m.d 1 5) (by simp) with h19339 | h19339
                                    · rcases p19334_3 (m.d 2 5) (by simp) with h19340 | h19340
                                      · linarith only [h19112, h19340, hlam]
                                      · linarith only [h19123, h19340, hlam]
                                    · linarith only [h19120, h19339, hlam]
                                  · linarith only [h19114, h19338, hlam]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19113, h19115, h19125, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h17994, hc01, hc15, hlam, hphi, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19118, h19124, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  rcases p19334_3 (m.d 0 5) (by simp) with h19349 | h19349
                                  · linarith only [h17994, h19349, hlam]
                                  · linarith only [h19114, h19349, hlam]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19112, hlam, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19118, hlam, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h0, h19112, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h0, h19110, h19122, h19124, h19125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19114, hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19120, hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19123, hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19125, hlam, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19115, hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19121, hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19124, hlam, p19334_0]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [h19125, hc34, hc45, hlam, hphi, p19334_1]
                                · have p19334_0 := h19334c.1
                                  have p19334_1 := h19334c.2.1
                                  have p19334_2 := h19334c.2.2.1
                                  have p19334_3 := h19334c.2.2.2
                                  linarith only [hlam, p19334_0]
                          · linarith only [h19329, hlam, p19286_0]
                        · linarith only [h19120, h19328, hlam]
                      · linarith only [h19114, h19327, hlam]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19113, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19119, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19122, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19125, hlam, p19286_1]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19114, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19120, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h19123, hlam, p19286_0]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [h0, h19110, h19123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19286_1]
                    · have p19286_0 := h19286c.1
                      have p19286_1 := h19286c.2.1
                      have p19286_2 := h19286c.2.2.1
                      have p19286_3 := h19286c.2.2.2
                      linarith only [hlam, p19286_0]
                  · linarith only [h19285, hlam, p19235_0]
                · linarith only [h16563, h19284, hlam]
              · linarith only [h14799, h19283, hlam]
            · linarith only [h0, h19282, hlam]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h19118, hlam, p19235_1]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h19120, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [h19121, hlam, p19235_0]
        · have p19235_0 := h19235c.1
          have p19235_1 := h19235c.2.1
          have p19235_2 := h19235c.2.2.1
          have p19235_3 := h19235c.2.2.2
          linarith only [hlam, p19235_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h19389 | h19389
      · linarith only [h0, h19110, h19122, h19124, h19389, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c | h19391c
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h0, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h14799, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h16563, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h17994, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          rcases p19391_3 (m.d 0 1) (by simp) with h19397 | h19397
          · linarith only [h19397, hlam, p19391_0]
          · rcases p19391_3 (m.d 1 2) (by simp) with h19399 | h19399
            · rcases p19391_3 (m.d 1 3) (by simp) with h19400 | h19400
              · linarith only [h19116, h19400, hlam]
              · linarith only [h14799, h19400, hlam]
            · linarith only [h19399, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h14799, hc01, hc12, hlam, hphi, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h17994, h19121, hc01, hc12, hlam, hphi, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          rcases p19391_3 (m.d 0 1) (by simp) with h19408 | h19408
          · linarith only [h19408, hlam, p19391_0]
          · rcases p19391_3 (m.d 1 2) (by simp) with h19410 | h19410
            · rcases p19391_3 (m.d 1 3) (by simp) with h19411 | h19411
              · rcases p19391_3 (m.d 1 4) (by simp) with h19412 | h19412
                · linarith only [h19119, h19412, hlam]
                · linarith only [h16563, h19412, hlam]
              · linarith only [h19411, hlam, p19391_0]
            · linarith only [h0, h19410, hlam]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h19116, hlam, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h16563, hc01, hc13, hlam, hphi, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h17994, h19116, hc01, hc12, hlam, hphi, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          rcases p19391_3 (m.d 0 1) (by simp) with h19421 | h19421
          · linarith only [h19421, hlam, p19391_0]
          · rcases p19391_3 (m.d 1 2) (by simp) with h19423 | h19423
            · rcases p19391_3 (m.d 1 3) (by simp) with h19424 | h19424
              · rcases p19391_3 (m.d 1 4) (by simp) with h19425 | h19425
                · rcases p19391_3 (m.d 1 5) (by simp) with h19426 | h19426
                  · linarith only [h19121, h19426, hlam]
                  · linarith only [h17994, h19426, hlam]
                · linarith only [h19425, hlam, p19391_0]
              · linarith only [h14799, h19424, hlam]
            · linarith only [h0, h19423, hlam]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h19117, hlam, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h19119, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h17994, hc01, hc14, hlam, hphi, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          rcases p19391_3 (m.d 0 1) (by simp) with h19436 | h19436
          · linarith only [h19436, hlam, p19391_0]
          · rcases p19391_3 (m.d 1 2) (by simp) with h19438 | h19438
            · rcases p19391_3 (m.d 1 3) (by simp) with h19439 | h19439
              · rcases p19391_3 (m.d 1 4) (by simp) with h19440 | h19440
                · rcases p19391_3 (m.d 1 5) (by simp) with h19441 | h19441
                  · rcases h3bigk with h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c | h19442c
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h14799, hlam, p19442_1]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19445 | h19445
                      · rcases p19442_3 (m.d 1 3) (by simp) with h19446 | h19446
                        · rcases p19442_3 (m.d 2 3) (by simp) with h19447 | h19447
                          · linarith only [h19110, h19447, hlam]
                          · rcases p19442_3 (m.d 3 4) (by simp) with h19449 | h19449
                            · linarith only [h19113, h19449, hlam]
                            · rcases p19442_3 (m.d 3 5) (by simp) with h19451 | h19451
                              · linarith only [h19114, h19451, hlam]
                              · rcases h5bigk with h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c | h19453c
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h17994, hlam, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  rcases p19453_3 (m.d 0 5) (by simp) with h19456 | h19456
                                  · rcases p19453_3 (m.d 1 5) (by simp) with h19457 | h19457
                                    · rcases p19453_3 (m.d 2 5) (by simp) with h19458 | h19458
                                      · linarith only [h19112, h19458, hlam]
                                      · rcases p19453_3 (m.d 3 5) (by simp) with h19460 | h19460
                                        · linarith only [h19114, h19460, hlam]
                                        · rcases p19453_3 (m.d 4 5) (by simp) with h19462 | h19462
                                          · linarith only [h19115, h19462, hlam]
                                          · linarith only [h19124, h19462, hlam]
                                    · linarith only [h19118, h19457, hlam]
                                  · linarith only [h19112, h19456, hlam]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  rcases p19453_3 (m.d 0 5) (by simp) with h19467 | h19467
                                  · rcases p19453_3 (m.d 1 5) (by simp) with h19468 | h19468
                                    · rcases p19453_3 (m.d 2 5) (by simp) with h19469 | h19469
                                      · linarith only [h19112, h19469, hlam]
                                      · linarith only [h19123, h19469, hlam]
                                    · linarith only [h19120, h19468, hlam]
                                  · linarith only [h19114, h19467, hlam]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h14799, h19113, h19115, h19116, h19122, h19124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h17994, hc01, hc15, hlam, hphi, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  rcases p19453_3 (m.d 0 5) (by simp) with h19477 | h19477
                                  · linarith only [h17994, h19477, hlam]
                                  · linarith only [h19112, h19477, hlam]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  rcases p19453_3 (m.d 0 5) (by simp) with h19480 | h19480
                                  · linarith only [h17994, h19480, hlam]
                                  · linarith only [h19114, h19480, hlam]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19122, h19124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19112, hlam, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19118, hlam, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19112, h19389, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19124, hlam, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19114, hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19120, hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19123, hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19389, hlam, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19115, hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h19121, hlam, p19453_0]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h14799, h19113, h19115, h19116, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [h14799, h19113, h19115, h19116, h19389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19453_1]
                                · have p19453_0 := h19453c.1
                                  have p19453_1 := h19453c.2.1
                                  have p19453_2 := h19453c.2.2.1
                                  have p19453_3 := h19453c.2.2.2
                                  linarith only [hlam, p19453_0]
                        · linarith only [h19116, h19446, hlam]
                      · linarith only [h19110, h19445, hlam]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19501 | h19501
                      · rcases p19442_3 (m.d 1 3) (by simp) with h19502 | h19502
                        · rcases p19442_3 (m.d 2 3) (by simp) with h19503 | h19503
                          · linarith only [h19110, h19503, hlam]
                          · linarith only [h19122, h19503, hlam]
                        · linarith only [h19119, h19502, hlam]
                      · linarith only [h19501, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19508 | h19508
                      · rcases p19442_3 (m.d 1 3) (by simp) with h19509 | h19509
                        · rcases p19442_3 (m.d 2 3) (by simp) with h19510 | h19510
                          · linarith only [h19110, h19510, hlam]
                          · linarith only [h19123, h19510, hlam]
                        · linarith only [h19120, h19509, hlam]
                      · linarith only [h19508, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19113, h19115, h19116, h19122, h19124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19442_1]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19517 | h19517
                      · linarith only [h14799, h19517, hlam]
                      · linarith only [h19110, h19517, hlam]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19520 | h19520
                      · linarith only [h14799, h19520, hlam]
                      · linarith only [h19113, h19520, hlam]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19523 | h19523
                      · linarith only [h14799, h19523, hlam]
                      · linarith only [h19114, h19523, hlam]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19110, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19116, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19529 | h19529
                      · rcases p19442_3 (m.d 1 3) (by simp) with h19530 | h19530
                        · rcases p19442_3 (m.d 2 3) (by simp) with h19531 | h19531
                          · rcases p19442_3 (m.d 3 4) (by simp) with h19532 | h19532
                            · linarith only [h19532, hlam, p19442_0]
                            · rcases p19442_3 (m.d 3 5) (by simp) with h19534 | h19534
                              · linarith only [h19123, h19534, hlam]
                              · linarith only [h19389, h19534, hlam]
                          · linarith only [h19531, hlam, p19442_0]
                        · linarith only [h19119, h19530, hlam]
                      · linarith only [h19113, h19529, hlam]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      rcases p19442_3 (m.d 0 3) (by simp) with h19540 | h19540
                      · rcases p19442_3 (m.d 1 3) (by simp) with h19541 | h19541
                        · rcases p19442_3 (m.d 2 3) (by simp) with h19542 | h19542
                          · rcases p19442_3 (m.d 3 4) (by simp) with h19543 | h19543
                            · linarith only [h19122, h19543, hlam]
                            · rcases p19442_3 (m.d 3 5) (by simp) with h19545 | h19545
                              · linarith only [h19545, hlam, p19442_0]
                              · rcases h5bigk with h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c | h19547c
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h17994, hlam, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  rcases p19547_3 (m.d 0 5) (by simp) with h19550 | h19550
                                  · rcases p19547_3 (m.d 1 5) (by simp) with h19551 | h19551
                                    · rcases p19547_3 (m.d 2 5) (by simp) with h19552 | h19552
                                      · linarith only [h19112, h19552, hlam]
                                      · rcases p19547_3 (m.d 3 5) (by simp) with h19554 | h19554
                                        · linarith only [h19114, h19554, hlam]
                                        · rcases p19547_3 (m.d 4 5) (by simp) with h19556 | h19556
                                          · linarith only [h19115, h19556, hlam]
                                          · linarith only [h19124, h19556, hlam]
                                    · linarith only [h19118, h19551, hlam]
                                  · linarith only [h19112, h19550, hlam]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  rcases p19547_3 (m.d 0 5) (by simp) with h19561 | h19561
                                  · rcases p19547_3 (m.d 1 5) (by simp) with h19562 | h19562
                                    · rcases p19547_3 (m.d 2 5) (by simp) with h19563 | h19563
                                      · linarith only [h19112, h19563, hlam]
                                      · linarith only [h19123, h19563, hlam]
                                    · linarith only [h19120, h19562, hlam]
                                  · linarith only [h19114, h19561, hlam]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19113, h19115, h19122, h19124, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h17994, h19119, h19121, hc01, hc13, hlam, hphi, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  rcases p19547_3 (m.d 0 5) (by simp) with h19571 | h19571
                                  · linarith only [h17994, h19571, hlam]
                                  · linarith only [h19112, h19571, hlam]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  rcases p19547_3 (m.d 0 5) (by simp) with h19574 | h19574
                                  · linarith only [h17994, h19574, hlam]
                                  · linarith only [h19114, h19574, hlam]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19122, h19124, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19112, hlam, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19118, hlam, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h0, h19112, h19389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19124, hlam, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19114, hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19120, hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19123, hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19389, hlam, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19115, hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19121, hlam, p19547_0]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h0, h19110, h19113, h19115, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [h19389, hc34, hc45, hlam, hphi, p19547_1]
                                · have p19547_0 := h19547c.1
                                  have p19547_1 := h19547c.2.1
                                  have p19547_2 := h19547c.2.2.1
                                  have p19547_3 := h19547c.2.2.2
                                  linarith only [hlam, p19547_0]
                          · linarith only [h19542, hlam, p19442_0]
                        · linarith only [h19120, h19541, hlam]
                      · linarith only [h19114, h19540, hlam]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19113, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19119, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19122, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19389, hlam, p19442_1]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19114, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19120, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h19123, hlam, p19442_0]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [h0, h19110, h19123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19442_1]
                    · have p19442_0 := h19442c.1
                      have p19442_1 := h19442c.2.1
                      have p19442_2 := h19442c.2.2.1
                      have p19442_3 := h19442c.2.2.2
                      linarith only [hlam, p19442_0]
                  · linarith only [h19441, hlam, p19391_0]
                · linarith only [h16563, h19440, hlam]
              · linarith only [h14799, h19439, hlam]
            · linarith only [h0, h19438, hlam]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h19118, hlam, p19391_1]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h19120, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [h19121, hlam, p19391_0]
        · have p19391_0 := h19391c.1
          have p19391_1 := h19391c.2.1
          have p19391_2 := h19391c.2.2.1
          have p19391_3 := h19391c.2.2.2
          linarith only [hlam, p19391_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h19614 | h19614
    · linarith only [h19122, h19123, h19614, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h19616 | h19616
      · linarith only [h0, h19110, h19122, h19614, h19616, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c | h19618c
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h0, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h14799, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h16563, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h17994, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          rcases p19618_3 (m.d 0 1) (by simp) with h19624 | h19624
          · linarith only [h19624, hlam, p19618_0]
          · rcases p19618_3 (m.d 1 2) (by simp) with h19626 | h19626
            · rcases p19618_3 (m.d 1 3) (by simp) with h19627 | h19627
              · linarith only [h19116, h19627, hlam]
              · linarith only [h14799, h19627, hlam]
            · linarith only [h19626, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h14799, hc01, hc12, hlam, hphi, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h16563, hc01, hc12, hlam, hphi, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          rcases p19618_3 (m.d 0 1) (by simp) with h19635 | h19635
          · linarith only [h19635, hlam, p19618_0]
          · rcases p19618_3 (m.d 1 2) (by simp) with h19637 | h19637
            · rcases p19618_3 (m.d 1 3) (by simp) with h19638 | h19638
              · rcases p19618_3 (m.d 1 4) (by simp) with h19639 | h19639
                · linarith only [h19119, h19639, hlam]
                · linarith only [h16563, h19639, hlam]
              · linarith only [h19638, hlam, p19618_0]
            · linarith only [h0, h19637, hlam]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h19116, hlam, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h16563, hc01, hc13, hlam, hphi, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h17994, h19115, h19116, h19122, h19123, h19616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          rcases p19618_3 (m.d 0 1) (by simp) with h19648 | h19648
          · linarith only [h19648, hlam, p19618_0]
          · rcases p19618_3 (m.d 1 2) (by simp) with h19650 | h19650
            · rcases p19618_3 (m.d 1 3) (by simp) with h19651 | h19651
              · rcases p19618_3 (m.d 1 4) (by simp) with h19652 | h19652
                · rcases p19618_3 (m.d 1 5) (by simp) with h19653 | h19653
                  · linarith only [h19121, h19653, hlam]
                  · linarith only [h17994, h19653, hlam]
                · linarith only [h19652, hlam, p19618_0]
              · linarith only [h14799, h19651, hlam]
            · linarith only [h0, h19650, hlam]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h19117, hlam, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h19119, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h17994, h19115, h19122, h19123, h19616, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          rcases p19618_3 (m.d 0 1) (by simp) with h19663 | h19663
          · linarith only [h19663, hlam, p19618_0]
          · rcases p19618_3 (m.d 1 2) (by simp) with h19665 | h19665
            · rcases p19618_3 (m.d 1 3) (by simp) with h19666 | h19666
              · rcases p19618_3 (m.d 1 4) (by simp) with h19667 | h19667
                · rcases p19618_3 (m.d 1 5) (by simp) with h19668 | h19668
                  · rcases h3bigk with h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c | h19669c
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h14799, hlam, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      rcases p19669_3 (m.d 0 3) (by simp) with h19672 | h19672
                      · rcases p19669_3 (m.d 1 3) (by simp) with h19673 | h19673
                        · rcases p19669_3 (m.d 2 3) (by simp) with h19674 | h19674
                          · linarith only [h19110, h19674, hlam]
                          · rcases p19669_3 (m.d 3 4) (by simp) with h19676 | h19676
                            · linarith only [h19113, h19676, hlam]
                            · rcases p19669_3 (m.d 3 5) (by simp) with h19678 | h19678
                              · linarith only [h19114, h19678, hlam]
                              · linarith only [h19123, h19678, hlam]
                        · linarith only [h19116, h19673, hlam]
                      · linarith only [h19110, h19672, hlam]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19113, h19115, h19122, h19123, h19616, hlam, p19669_2]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19122, h19123, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19113, h19115, h19116, h19122, h19123, h19616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      rcases p19669_3 (m.d 0 3) (by simp) with h19687 | h19687
                      · linarith only [h14799, h19687, hlam]
                      · linarith only [h19110, h19687, hlam]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h14799, h19113, h19115, h19122, h19123, h19616, hlam, p19669_2]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19122, h19123, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19110, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19116, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19113, h19115, h19123, h19616, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19123, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19113, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19119, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19122, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19616, hlam, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19114, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h19120, hlam, p19669_0]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [h0, h19110, h19113, h19115, h19122, h19616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19669_1]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      rcases p19669_3 (m.d 0 3) (by simp) with h19705 | h19705
                      · rcases p19669_3 (m.d 1 3) (by simp) with h19706 | h19706
                        · rcases p19669_3 (m.d 2 3) (by simp) with h19707 | h19707
                          · linarith only [h19123, h19707, hlam]
                          · linarith only [h19122, h19707, hlam]
                        · linarith only [h19119, h19706, hlam]
                      · linarith only [h19113, h19705, hlam]
                    · have p19669_0 := h19669c.1
                      have p19669_1 := h19669c.2.1
                      have p19669_2 := h19669c.2.2.1
                      have p19669_3 := h19669c.2.2.2
                      linarith only [hlam, p19669_0]
                  · linarith only [h19668, hlam, p19618_0]
                · linarith only [h16563, h19667, hlam]
              · linarith only [h14799, h19666, hlam]
            · linarith only [h0, h19665, hlam]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h19118, hlam, p19618_1]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h19120, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [h19121, hlam, p19618_0]
        · have p19618_0 := h19618c.1
          have p19618_1 := h19618c.2.1
          have p19618_2 := h19618c.2.2.1
          have p19618_3 := h19618c.2.2.2
          linarith only [hlam, p19618_0]

end R2N4
