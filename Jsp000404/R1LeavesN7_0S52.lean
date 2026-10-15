import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S49
import Jsp000404.R1LeavesN7_0S50
import Jsp000404.R1LeavesN7_0S51

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h30184 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h30186 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h30188 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 2 3 4 (by decide) (by decide) with h31157 | h31157
  · linarith only [h23337, h30177, h30178, h30184, h30188, h31157, hc12, hc23, hlam, hphi]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h31159 | h31159
    · linarith only [h29475, h31157, h31159, hc03, hc34, hlam, hphi]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h31161 | h31161
      · rcases m.htr 3 4 5 (by decide) (by decide) with h31162 | h31162
        · rcases h1bigk with h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c | h31163c
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            rcases p31163_3 (m.d 0 1) (by simp) with h31165 | h31165
            · rcases p31163_3 (m.d 1 2) (by simp) with h31166 | h31166
              · linarith only [h31166, hlam, p31163_0]
              · rcases p31163_3 (m.d 1 3) (by simp) with h31168 | h31168
                · linarith only [h1, h31168, hlam]
                · linarith only [h30178, h31168, hlam]
            · linarith only [h31165, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            rcases p31163_3 (m.d 0 1) (by simp) with h31172 | h31172
            · rcases p31163_3 (m.d 1 2) (by simp) with h31173 | h31173
              · linarith only [h0, h31173, hlam]
              · rcases p31163_3 (m.d 1 3) (by simp) with h31175 | h31175
                · linarith only [h31175, hlam, p31163_0]
                · rcases p31163_3 (m.d 1 4) (by simp) with h31177 | h31177
                  · linarith only [h2, h31177, hlam]
                  · linarith only [h30184, h31177, hlam]
            · linarith only [h31172, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            rcases p31163_3 (m.d 0 1) (by simp) with h31181 | h31181
            · rcases p31163_3 (m.d 1 2) (by simp) with h31182 | h31182
              · linarith only [h0, h31182, hlam]
              · rcases p31163_3 (m.d 1 3) (by simp) with h31184 | h31184
                · linarith only [h1, h31184, hlam]
                · rcases p31163_3 (m.d 1 4) (by simp) with h31186 | h31186
                  · linarith only [h31186, hlam, p31163_0]
                  · rcases p31163_3 (m.d 1 5) (by simp) with h31188 | h31188
                    · linarith only [h3, h31188, hlam]
                    · linarith only [h30188, h31188, hlam]
            · linarith only [h31181, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            rcases p31163_3 (m.d 0 1) (by simp) with h31192 | h31192
            · rcases p31163_3 (m.d 1 2) (by simp) with h31193 | h31193
              · linarith only [h0, h31193, hlam]
              · rcases p31163_3 (m.d 1 3) (by simp) with h31195 | h31195
                · linarith only [h1, h31195, hlam]
                · rcases p31163_3 (m.d 1 4) (by simp) with h31197 | h31197
                  · linarith only [h2, h31197, hlam]
                  · rcases p31163_3 (m.d 1 5) (by simp) with h31199 | h31199
                    · linarith only [h31199, hlam, p31163_0]
                    · rcases h1emax with h31201 | h31201 | h31201 | h31201 | h31201
                      · linarith only [h31201, hc15, hlam, hphi, ht01, ht0b, ht5b, p31163_1]
                      · rcases h2bigk with h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c | h31203c
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h31159, h31162, h4, hc12, hc34, hlam, hphi, ht23, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h4, hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h19744, hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h22010, hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h0, hlam, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h30178, hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h30180, hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h30182, hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h31159, h31162, hc02, hc34, hlam, hphi, ht23, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h31159, h31162, hc12, hc34, hlam, hphi, ht23, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h31157, hlam, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h31159, hlam, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          rcases p31203_3 (m.d 0 2) (by simp) with h31219 | h31219
                          · linarith only [h31219, hlam, p31203_0]
                          · rcases p31203_3 (m.d 1 2) (by simp) with h31221 | h31221
                            · linarith only [h30180, h31221, hlam]
                            · rcases p31203_3 (m.d 2 3) (by simp) with h31223 | h31223
                              · linarith only [h31157, h31223, hlam]
                              · linarith only [h31223, h4, hlam]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          rcases p31203_3 (m.d 0 2) (by simp) with h31226 | h31226
                          · linarith only [h19744, h31226, hlam]
                          · linarith only [h0, h31226, hlam]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h0, h4, hc12, hc24, hlam, hphi, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [hlam, p31203_0]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h0, h22010, hc12, hc24, hlam, hphi, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          rcases p31203_3 (m.d 0 2) (by simp) with h31232 | h31232
                          · linarith only [h31232, hlam, p31203_0]
                          · rcases p31203_3 (m.d 1 2) (by simp) with h31234 | h31234
                            · linarith only [h30182, h31234, hlam]
                            · rcases p31203_3 (m.d 2 3) (by simp) with h31236 | h31236
                              · linarith only [h31159, h31236, hlam]
                              · linarith only [h31236, h4, hlam]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          rcases p31203_3 (m.d 0 2) (by simp) with h31239 | h31239
                          · linarith only [h22010, h31239, hlam]
                          · linarith only [h0, h31239, hlam]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [h31161, hlam, p31203_1]
                        · have p31203_0 := h31203c.1
                          have p31203_1 := h31203c.2.1
                          have p31203_2 := h31203c.2.2.1
                          have p31203_3 := h31203c.2.2.2
                          linarith only [hlam, p31203_0]
                      · rcases h2bigk with h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c | h31245c
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h4, hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h19744, hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h22010, hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h0, hlam, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h30178, hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h30180, hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h30182, hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h31157, hc02, hc34, hlam, hphi, ht23, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h31157, hc12, hc34, hlam, hphi, ht23, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h31157, hlam, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h31159, hlam, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          rcases p31245_3 (m.d 0 2) (by simp) with h31261 | h31261
                          · linarith only [h31261, hlam, p31245_0]
                          · rcases p31245_3 (m.d 1 2) (by simp) with h31263 | h31263
                            · linarith only [h30180, h31263, hlam]
                            · rcases p31245_3 (m.d 2 3) (by simp) with h31265 | h31265
                              · linarith only [h31157, h31265, hlam]
                              · linarith only [h31265, h4, hlam]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          rcases p31245_3 (m.d 0 2) (by simp) with h31268 | h31268
                          · linarith only [h19744, h31268, hlam]
                          · linarith only [h0, h31268, hlam]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h0, h31157, h4, hc12, hc34, hlam, hphi, ht23, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [hlam, p31245_0]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h0, h22010, h31157, hc12, hc34, hlam, hphi, ht23, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          rcases p31245_3 (m.d 0 2) (by simp) with h31274 | h31274
                          · linarith only [h31274, hlam, p31245_0]
                          · rcases p31245_3 (m.d 1 2) (by simp) with h31276 | h31276
                            · linarith only [h30182, h31276, hlam]
                            · rcases p31245_3 (m.d 2 3) (by simp) with h31278 | h31278
                              · linarith only [h31159, h31278, hlam]
                              · linarith only [h31278, h4, hlam]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          rcases p31245_3 (m.d 0 2) (by simp) with h31281 | h31281
                          · linarith only [h22010, h31281, hlam]
                          · linarith only [h0, h31281, hlam]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [h31161, hlam, p31245_1]
                        · have p31245_0 := h31245c.1
                          have p31245_1 := h31245c.2.1
                          have p31245_2 := h31245c.2.2.1
                          have p31245_3 := h31245c.2.2.2
                          linarith only [hlam, p31245_0]
                      · rcases h2bigk with h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c | h31287c
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h4, hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h19744, hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h22010, hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h0, hlam, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h30178, hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h30180, hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h30182, hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h31157, hc02, hc34, hlam, hphi, ht23, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h31157, hc12, hc34, hlam, hphi, ht23, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h31157, hlam, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h31159, hlam, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          rcases p31287_3 (m.d 0 2) (by simp) with h31303 | h31303
                          · linarith only [h31303, hlam, p31287_0]
                          · rcases p31287_3 (m.d 1 2) (by simp) with h31305 | h31305
                            · linarith only [h30180, h31305, hlam]
                            · rcases p31287_3 (m.d 2 3) (by simp) with h31307 | h31307
                              · linarith only [h31157, h31307, hlam]
                              · linarith only [h31307, h4, hlam]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          rcases p31287_3 (m.d 0 2) (by simp) with h31310 | h31310
                          · linarith only [h19744, h31310, hlam]
                          · linarith only [h0, h31310, hlam]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h0, h31157, h4, hc12, hc34, hlam, hphi, ht23, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [hlam, p31287_0]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h0, h22010, h31157, hc12, hc34, hlam, hphi, ht23, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          rcases p31287_3 (m.d 0 2) (by simp) with h31316 | h31316
                          · linarith only [h31316, hlam, p31287_0]
                          · rcases p31287_3 (m.d 1 2) (by simp) with h31318 | h31318
                            · linarith only [h30182, h31318, hlam]
                            · rcases p31287_3 (m.d 2 3) (by simp) with h31320 | h31320
                              · linarith only [h31159, h31320, hlam]
                              · linarith only [h31320, h4, hlam]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          rcases p31287_3 (m.d 0 2) (by simp) with h31323 | h31323
                          · linarith only [h22010, h31323, hlam]
                          · linarith only [h0, h31323, hlam]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [h31161, hlam, p31287_1]
                        · have p31287_0 := h31287c.1
                          have p31287_1 := h31287c.2.1
                          have p31287_2 := h31287c.2.2.1
                          have p31287_3 := h31287c.2.2.2
                          linarith only [hlam, p31287_0]
                      · rcases h2bigk with h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c | h31329c
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h4, hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h19744, hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h22010, hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h0, hlam, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h30178, hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h30180, hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h30182, hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h31157, hc02, hc34, hlam, hphi, ht23, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h31157, hc12, hc34, hlam, hphi, ht23, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h31157, hlam, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h31159, hlam, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          rcases p31329_3 (m.d 0 2) (by simp) with h31345 | h31345
                          · linarith only [h31345, hlam, p31329_0]
                          · rcases p31329_3 (m.d 1 2) (by simp) with h31347 | h31347
                            · linarith only [h30180, h31347, hlam]
                            · rcases p31329_3 (m.d 2 3) (by simp) with h31349 | h31349
                              · linarith only [h31157, h31349, hlam]
                              · linarith only [h31349, h4, hlam]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          rcases p31329_3 (m.d 0 2) (by simp) with h31352 | h31352
                          · linarith only [h19744, h31352, hlam]
                          · linarith only [h0, h31352, hlam]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h0, h31157, h4, hc12, hc34, hlam, hphi, ht23, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [hlam, p31329_0]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h0, h22010, h31157, hc12, hc34, hlam, hphi, ht23, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          rcases p31329_3 (m.d 0 2) (by simp) with h31358 | h31358
                          · linarith only [h31358, hlam, p31329_0]
                          · rcases p31329_3 (m.d 1 2) (by simp) with h31360 | h31360
                            · linarith only [h30182, h31360, hlam]
                            · rcases p31329_3 (m.d 2 3) (by simp) with h31362 | h31362
                              · linarith only [h31159, h31362, hlam]
                              · linarith only [h31362, h4, hlam]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          rcases p31329_3 (m.d 0 2) (by simp) with h31365 | h31365
                          · linarith only [h22010, h31365, hlam]
                          · linarith only [h0, h31365, hlam]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h0, h4, hc12, hc25, hlam, hphi, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [h31161, hlam, p31329_1]
                        · have p31329_0 := h31329c.1
                          have p31329_1 := h31329c.2.1
                          have p31329_2 := h31329c.2.2.1
                          have p31329_3 := h31329c.2.2.2
                          linarith only [hlam, p31329_0]
            · linarith only [h31192, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h0, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30178, hlam, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30180, hlam, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30182, hlam, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h1, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30184, h30188, hc12, hc45, hlam, hphi, ht23, ht34, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30184, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30186, hlam, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h2, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h19744, h30177, h30188, h31157, hc12, hc34, hlam, hphi, ht23, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h19744, h30177, h30188, h31157, hc13, hc34, hlam, hphi, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h30188, hlam, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h3, hlam, p31163_0]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h19744, h30177, h30188, h31157, hc12, hc34, hlam, hphi, ht23, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h19744, h30177, h30178, h30188, h31157, hc12, hc34, hlam, hphi, ht23, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [h19744, h30177, h30180, h30188, h31157, hc12, hc34, hlam, hphi, ht23, p31163_1]
          · have p31163_0 := h31163c.1
            have p31163_1 := h31163c.2.1
            have p31163_2 := h31163c.2.2.1
            have p31163_3 := h31163c.2.2.2
            linarith only [hlam, p31163_0]
        · linarith only [h19744, h30177, h31157, h31162, hlam]
      · linarith only [h19744, h30177, h31161, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h30184 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h30186 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 1 4 5 (by decide) (by decide) with h30188 | h30188
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184 h30186 h30188
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184 h30186 h30188

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h30184 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 1 3 5 (by decide) (by decide) with h30186 | h30186
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184 h30186
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184 h30186

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h30182 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 1 3 4 (by decide) (by decide) with h30184 | h30184
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182 h30184

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h30180 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 1 2 5 (by decide) (by decide) with h30182 | h30182
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180 h30182

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h30178 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 1 2 4 (by decide) (by decide) with h30180 | h30180
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178 h30180

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  rcases m.htr 1 2 3 (by decide) (by decide) with h30178 | h30178
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177 h30178

end R2N4
