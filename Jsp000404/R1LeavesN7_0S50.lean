import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x0 (m : N7Model)
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
    (h30186 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  linarith only [h1, h29475, h30186, hlam]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1_x1_x1_x1_x1_x0_x0 (m : N7Model)
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
    (h30188 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h30189 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h30190 | h30190
  · rcases m.htr 2 4 5 (by decide) (by decide) with h30191 | h30191
    · rcases m.htr 3 4 5 (by decide) (by decide) with h30192 | h30192
      · rcases h1bigk with h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c | h30193c
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          rcases p30193_3 (m.d 0 1) (by simp) with h30195 | h30195
          · rcases p30193_3 (m.d 1 2) (by simp) with h30196 | h30196
            · linarith only [h30196, hlam, p30193_0]
            · rcases p30193_3 (m.d 1 3) (by simp) with h30198 | h30198
              · linarith only [h1, h30198, hlam]
              · linarith only [h30178, h30198, hlam]
          · linarith only [h30195, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          rcases p30193_3 (m.d 0 1) (by simp) with h30202 | h30202
          · rcases p30193_3 (m.d 1 2) (by simp) with h30203 | h30203
            · linarith only [h0, h30203, hlam]
            · rcases p30193_3 (m.d 1 3) (by simp) with h30205 | h30205
              · linarith only [h30205, hlam, p30193_0]
              · rcases p30193_3 (m.d 1 4) (by simp) with h30207 | h30207
                · linarith only [h2, h30207, hlam]
                · linarith only [h30184, h30207, hlam]
          · linarith only [h30202, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          rcases p30193_3 (m.d 0 1) (by simp) with h30211 | h30211
          · rcases p30193_3 (m.d 1 2) (by simp) with h30212 | h30212
            · linarith only [h0, h30212, hlam]
            · rcases p30193_3 (m.d 1 3) (by simp) with h30214 | h30214
              · linarith only [h1, h30214, hlam]
              · rcases p30193_3 (m.d 1 4) (by simp) with h30216 | h30216
                · linarith only [h30216, hlam, p30193_0]
                · rcases p30193_3 (m.d 1 5) (by simp) with h30218 | h30218
                  · linarith only [h3, h30218, hlam]
                  · rcases h1emax with h30220 | h30220 | h30220 | h30220 | h30220
                    · linarith only [h30186, h30188, h30220, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30193_1]
                    · rcases h2bigk with h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c | h30222c
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h29475, h30189, h30192, h4, hc12, hc23, hlam, hphi, p30222_1]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h4, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h19744, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h22010, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h0, hlam, p30222_1]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h30178, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h30180, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h30182, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        rcases p30222_3 (m.d 0 2) (by simp) with h30233 | h30233
                        · linarith only [h30233, hlam, p30222_0]
                        · rcases p30222_3 (m.d 1 2) (by simp) with h30235 | h30235
                          · linarith only [h30178, h30235, hlam]
                          · rcases p30222_3 (m.d 2 3) (by simp) with h30237 | h30237
                            · rcases p30222_3 (m.d 2 4) (by simp) with h30238 | h30238
                              · linarith only [h30189, h30238, hlam]
                              · linarith only [h19744, h30238, hlam]
                            · linarith only [h30237, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        rcases p30222_3 (m.d 0 2) (by simp) with h30242 | h30242
                        · linarith only [h30242, h4, hlam]
                        · linarith only [h0, h30242, hlam]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h19744, hc02, hc23, hlam, hphi, p30222_1]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h1, h29475, h30178, h30190, hc12, hc23, hlam, hphi, p30222_1]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        rcases p30222_3 (m.d 0 2) (by simp) with h30248 | h30248
                        · linarith only [h30248, hlam, p30222_0]
                        · rcases p30222_3 (m.d 1 2) (by simp) with h30250 | h30250
                          · linarith only [h30180, h30250, hlam]
                          · rcases p30222_3 (m.d 2 3) (by simp) with h30252 | h30252
                            · rcases p30222_3 (m.d 2 4) (by simp) with h30253 | h30253
                              · rcases p30222_3 (m.d 2 5) (by simp) with h30254 | h30254
                                · linarith only [h30191, h30254, hlam]
                                · linarith only [h22010, h30254, hlam]
                              · linarith only [h30253, hlam, p30222_0]
                            · linarith only [h30252, h4, hlam]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        rcases p30222_3 (m.d 0 2) (by simp) with h30259 | h30259
                        · linarith only [h19744, h30259, hlam]
                        · linarith only [h0, h30259, hlam]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h30189, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h1, h29475, h30178, h30190, hc12, hc24, hlam, hphi, p30222_1]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        rcases p30222_3 (m.d 0 2) (by simp) with h30265 | h30265
                        · linarith only [h30265, hlam, p30222_0]
                        · rcases p30222_3 (m.d 1 2) (by simp) with h30267 | h30267
                          · linarith only [h30182, h30267, hlam]
                          · rcases p30222_3 (m.d 2 3) (by simp) with h30269 | h30269
                            · rcases p30222_3 (m.d 2 4) (by simp) with h30270 | h30270
                              · rcases p30222_3 (m.d 2 5) (by simp) with h30271 | h30271
                                · rcases h4bigk with h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c | h30272c
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h23337, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h19744, hlam, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h23337, hlam, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    rcases p30272_3 (m.d 0 4) (by simp) with h30277 | h30277
                                    · rcases p30272_3 (m.d 1 4) (by simp) with h30278 | h30278
                                      · linarith only [h2, h30278, hlam]
                                      · linarith only [h30188, h30278, hlam]
                                    · linarith only [h30277, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h2, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30180, hlam, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30184, hlam, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p30193_1, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    rcases p30272_3 (m.d 0 4) (by simp) with h30287 | h30287
                                    · linarith only [h19744, h30287, hlam]
                                    · rcases p30272_3 (m.d 1 4) (by simp) with h30289 | h30289
                                      · linarith only [h30180, h30289, hlam]
                                      · rcases p30272_3 (m.d 2 4) (by simp) with h30291 | h30291
                                        · rcases p30272_3 (m.d 3 4) (by simp) with h30292 | h30292
                                          · linarith only [h30189, h30292, hlam]
                                          · linarith only [h23337, h30292, hlam]
                                        · linarith only [h19744, h30291, hlam]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    rcases p30272_3 (m.d 0 4) (by simp) with h30296 | h30296
                                    · linarith only [h19744, h30296, hlam]
                                    · linarith only [h2, h30296, hlam]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h1, h23337, h30178, h30189, hc12, hc23, hlam, hphi, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    rcases p30272_3 (m.d 0 4) (by simp) with h30301 | h30301
                                    · linarith only [h19744, h30301, hlam]
                                    · linarith only [h30177, h30301, hlam]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h2, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30272_1]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30189, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    rcases p30272_3 (m.d 0 4) (by simp) with h30308 | h30308
                                    · linarith only [h23337, h30308, hlam]
                                    · linarith only [h30177, h30308, hlam]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30177, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30188, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30191, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [h30192, hlam, p30272_0]
                                  · have p30272_0 := h30272c.1
                                    have p30272_1 := h30272c.2.1
                                    have p30272_2 := h30272c.2.2.1
                                    have p30272_3 := h30272c.2.2.2
                                    linarith only [hlam, p30272_0]
                                · linarith only [h30271, hlam, p30222_0]
                              · linarith only [h19744, h30270, hlam]
                            · linarith only [h30269, h4, hlam]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        rcases p30222_3 (m.d 0 2) (by simp) with h30319 | h30319
                        · linarith only [h22010, h30319, hlam]
                        · linarith only [h0, h30319, hlam]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h30190, hlam, p30222_0]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [h30191, hlam, p30222_1]
                      · have p30222_0 := h30222c.1
                        have p30222_1 := h30222c.2.1
                        have p30222_2 := h30222c.2.2.1
                        have p30222_3 := h30222c.2.2.2
                        linarith only [hlam, p30222_0]
                    · rcases h2bigk with h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c | h30325c
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30325_1]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h4, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h19744, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h22010, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h0, hlam, p30325_1]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h30178, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h30180, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h30182, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        rcases p30325_3 (m.d 0 2) (by simp) with h30336 | h30336
                        · linarith only [h30336, hlam, p30325_0]
                        · rcases p30325_3 (m.d 1 2) (by simp) with h30338 | h30338
                          · linarith only [h30178, h30338, hlam]
                          · rcases p30325_3 (m.d 2 3) (by simp) with h30340 | h30340
                            · rcases p30325_3 (m.d 2 4) (by simp) with h30341 | h30341
                              · linarith only [h30189, h30341, hlam]
                              · linarith only [h19744, h30341, hlam]
                            · linarith only [h30340, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        rcases p30325_3 (m.d 0 2) (by simp) with h30345 | h30345
                        · linarith only [h30345, h4, hlam]
                        · linarith only [h0, h30345, hlam]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h19744, hc02, hc23, hlam, hphi, p30325_1]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p30325_1]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        rcases p30325_3 (m.d 0 2) (by simp) with h30351 | h30351
                        · linarith only [h30351, hlam, p30325_0]
                        · rcases p30325_3 (m.d 1 2) (by simp) with h30353 | h30353
                          · linarith only [h30180, h30353, hlam]
                          · rcases p30325_3 (m.d 2 3) (by simp) with h30355 | h30355
                            · rcases p30325_3 (m.d 2 4) (by simp) with h30356 | h30356
                              · rcases p30325_3 (m.d 2 5) (by simp) with h30357 | h30357
                                · linarith only [h30191, h30357, hlam]
                                · linarith only [h22010, h30357, hlam]
                              · linarith only [h30356, hlam, p30325_0]
                            · linarith only [h30355, h4, hlam]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        rcases p30325_3 (m.d 0 2) (by simp) with h30362 | h30362
                        · linarith only [h19744, h30362, hlam]
                        · linarith only [h0, h30362, hlam]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h30189, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h1, h29475, h30178, h30190, hc12, hc24, hlam, hphi, p30325_1]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        rcases p30325_3 (m.d 0 2) (by simp) with h30368 | h30368
                        · linarith only [h30368, hlam, p30325_0]
                        · rcases p30325_3 (m.d 1 2) (by simp) with h30370 | h30370
                          · linarith only [h30182, h30370, hlam]
                          · rcases p30325_3 (m.d 2 3) (by simp) with h30372 | h30372
                            · rcases p30325_3 (m.d 2 4) (by simp) with h30373 | h30373
                              · rcases p30325_3 (m.d 2 5) (by simp) with h30374 | h30374
                                · rcases h4bigk with h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c | h30375c
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h23337, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h19744, hlam, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h23337, hlam, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    rcases p30375_3 (m.d 0 4) (by simp) with h30380 | h30380
                                    · rcases p30375_3 (m.d 1 4) (by simp) with h30381 | h30381
                                      · linarith only [h2, h30381, hlam]
                                      · linarith only [h30188, h30381, hlam]
                                    · linarith only [h30380, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h2, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30180, hlam, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30184, hlam, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p30193_1, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    rcases p30375_3 (m.d 0 4) (by simp) with h30390 | h30390
                                    · linarith only [h19744, h30390, hlam]
                                    · rcases p30375_3 (m.d 1 4) (by simp) with h30392 | h30392
                                      · linarith only [h30180, h30392, hlam]
                                      · rcases p30375_3 (m.d 2 4) (by simp) with h30394 | h30394
                                        · rcases p30375_3 (m.d 3 4) (by simp) with h30395 | h30395
                                          · linarith only [h30189, h30395, hlam]
                                          · linarith only [h23337, h30395, hlam]
                                        · linarith only [h19744, h30394, hlam]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    rcases p30375_3 (m.d 0 4) (by simp) with h30399 | h30399
                                    · linarith only [h19744, h30399, hlam]
                                    · linarith only [h2, h30399, hlam]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h1, h23337, h30178, h30189, hc12, hc23, hlam, hphi, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    rcases p30375_3 (m.d 0 4) (by simp) with h30404 | h30404
                                    · linarith only [h19744, h30404, hlam]
                                    · linarith only [h30177, h30404, hlam]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h2, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30375_1]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30189, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    rcases p30375_3 (m.d 0 4) (by simp) with h30411 | h30411
                                    · linarith only [h23337, h30411, hlam]
                                    · linarith only [h30177, h30411, hlam]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30177, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30188, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30191, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [h30192, hlam, p30375_0]
                                  · have p30375_0 := h30375c.1
                                    have p30375_1 := h30375c.2.1
                                    have p30375_2 := h30375c.2.2.1
                                    have p30375_3 := h30375c.2.2.2
                                    linarith only [hlam, p30375_0]
                                · linarith only [h30374, hlam, p30325_0]
                              · linarith only [h19744, h30373, hlam]
                            · linarith only [h30372, h4, hlam]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        rcases p30325_3 (m.d 0 2) (by simp) with h30422 | h30422
                        · linarith only [h22010, h30422, hlam]
                        · linarith only [h0, h30422, hlam]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h30190, hlam, p30325_0]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [h30191, hlam, p30325_1]
                      · have p30325_0 := h30325c.1
                        have p30325_1 := h30325c.2.1
                        have p30325_2 := h30325c.2.2.1
                        have p30325_3 := h30325c.2.2.2
                        linarith only [hlam, p30325_0]
                    · rcases h2bigk with h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c | h30428c
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30428_1]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h4, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h19744, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h22010, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h0, hlam, p30428_1]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h30178, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h30180, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h30182, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        rcases p30428_3 (m.d 0 2) (by simp) with h30439 | h30439
                        · linarith only [h30439, hlam, p30428_0]
                        · rcases p30428_3 (m.d 1 2) (by simp) with h30441 | h30441
                          · linarith only [h30178, h30441, hlam]
                          · rcases p30428_3 (m.d 2 3) (by simp) with h30443 | h30443
                            · rcases p30428_3 (m.d 2 4) (by simp) with h30444 | h30444
                              · linarith only [h30189, h30444, hlam]
                              · linarith only [h19744, h30444, hlam]
                            · linarith only [h30443, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        rcases p30428_3 (m.d 0 2) (by simp) with h30448 | h30448
                        · linarith only [h30448, h4, hlam]
                        · linarith only [h0, h30448, hlam]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h19744, hc02, hc23, hlam, hphi, p30428_1]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p30428_1]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        rcases p30428_3 (m.d 0 2) (by simp) with h30454 | h30454
                        · linarith only [h30454, hlam, p30428_0]
                        · rcases p30428_3 (m.d 1 2) (by simp) with h30456 | h30456
                          · linarith only [h30180, h30456, hlam]
                          · rcases p30428_3 (m.d 2 3) (by simp) with h30458 | h30458
                            · rcases p30428_3 (m.d 2 4) (by simp) with h30459 | h30459
                              · rcases p30428_3 (m.d 2 5) (by simp) with h30460 | h30460
                                · linarith only [h30191, h30460, hlam]
                                · linarith only [h22010, h30460, hlam]
                              · linarith only [h30459, hlam, p30428_0]
                            · linarith only [h30458, h4, hlam]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        rcases p30428_3 (m.d 0 2) (by simp) with h30465 | h30465
                        · linarith only [h19744, h30465, hlam]
                        · linarith only [h0, h30465, hlam]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h30189, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h1, h29475, h30178, h30190, hc12, hc24, hlam, hphi, p30428_1]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        rcases p30428_3 (m.d 0 2) (by simp) with h30471 | h30471
                        · linarith only [h30471, hlam, p30428_0]
                        · rcases p30428_3 (m.d 1 2) (by simp) with h30473 | h30473
                          · linarith only [h30182, h30473, hlam]
                          · rcases p30428_3 (m.d 2 3) (by simp) with h30475 | h30475
                            · rcases p30428_3 (m.d 2 4) (by simp) with h30476 | h30476
                              · rcases p30428_3 (m.d 2 5) (by simp) with h30477 | h30477
                                · rcases h4bigk with h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c | h30478c
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h23337, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h19744, hlam, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h23337, hlam, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    rcases p30478_3 (m.d 0 4) (by simp) with h30483 | h30483
                                    · rcases p30478_3 (m.d 1 4) (by simp) with h30484 | h30484
                                      · linarith only [h2, h30484, hlam]
                                      · linarith only [h30188, h30484, hlam]
                                    · linarith only [h30483, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h2, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30180, hlam, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30184, hlam, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p30193_1, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    rcases p30478_3 (m.d 0 4) (by simp) with h30493 | h30493
                                    · linarith only [h19744, h30493, hlam]
                                    · rcases p30478_3 (m.d 1 4) (by simp) with h30495 | h30495
                                      · linarith only [h30180, h30495, hlam]
                                      · rcases p30478_3 (m.d 2 4) (by simp) with h30497 | h30497
                                        · rcases p30478_3 (m.d 3 4) (by simp) with h30498 | h30498
                                          · linarith only [h30189, h30498, hlam]
                                          · linarith only [h23337, h30498, hlam]
                                        · linarith only [h19744, h30497, hlam]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    rcases p30478_3 (m.d 0 4) (by simp) with h30502 | h30502
                                    · linarith only [h19744, h30502, hlam]
                                    · linarith only [h2, h30502, hlam]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h1, h23337, h30178, h30189, hc12, hc23, hlam, hphi, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    rcases p30478_3 (m.d 0 4) (by simp) with h30507 | h30507
                                    · linarith only [h19744, h30507, hlam]
                                    · linarith only [h30177, h30507, hlam]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h2, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30478_1]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30189, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    rcases p30478_3 (m.d 0 4) (by simp) with h30514 | h30514
                                    · linarith only [h23337, h30514, hlam]
                                    · linarith only [h30177, h30514, hlam]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30177, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30188, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30191, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [h30192, hlam, p30478_0]
                                  · have p30478_0 := h30478c.1
                                    have p30478_1 := h30478c.2.1
                                    have p30478_2 := h30478c.2.2.1
                                    have p30478_3 := h30478c.2.2.2
                                    linarith only [hlam, p30478_0]
                                · linarith only [h30477, hlam, p30428_0]
                              · linarith only [h19744, h30476, hlam]
                            · linarith only [h30475, h4, hlam]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        rcases p30428_3 (m.d 0 2) (by simp) with h30525 | h30525
                        · linarith only [h22010, h30525, hlam]
                        · linarith only [h0, h30525, hlam]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h30190, hlam, p30428_0]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [h30191, hlam, p30428_1]
                      · have p30428_0 := h30428c.1
                        have p30428_1 := h30428c.2.1
                        have p30428_2 := h30428c.2.2.1
                        have p30428_3 := h30428c.2.2.2
                        linarith only [hlam, p30428_0]
                    · rcases h2bigk with h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c | h30531c
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p30531_1]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h4, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h19744, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h22010, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h0, hlam, p30531_1]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h30178, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h30180, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h30182, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        rcases p30531_3 (m.d 0 2) (by simp) with h30542 | h30542
                        · linarith only [h30542, hlam, p30531_0]
                        · rcases p30531_3 (m.d 1 2) (by simp) with h30544 | h30544
                          · linarith only [h30178, h30544, hlam]
                          · rcases p30531_3 (m.d 2 3) (by simp) with h30546 | h30546
                            · rcases p30531_3 (m.d 2 4) (by simp) with h30547 | h30547
                              · linarith only [h30189, h30547, hlam]
                              · linarith only [h19744, h30547, hlam]
                            · linarith only [h30546, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        rcases p30531_3 (m.d 0 2) (by simp) with h30551 | h30551
                        · linarith only [h30551, h4, hlam]
                        · linarith only [h0, h30551, hlam]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h19744, hc02, hc23, hlam, hphi, p30531_1]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h0, h22010, hc12, hc23, hlam, hphi, p30531_1]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        rcases p30531_3 (m.d 0 2) (by simp) with h30557 | h30557
                        · linarith only [h30557, hlam, p30531_0]
                        · rcases p30531_3 (m.d 1 2) (by simp) with h30559 | h30559
                          · linarith only [h30180, h30559, hlam]
                          · rcases p30531_3 (m.d 2 3) (by simp) with h30561 | h30561
                            · rcases p30531_3 (m.d 2 4) (by simp) with h30562 | h30562
                              · rcases p30531_3 (m.d 2 5) (by simp) with h30563 | h30563
                                · linarith only [h30191, h30563, hlam]
                                · linarith only [h22010, h30563, hlam]
                              · linarith only [h30562, hlam, p30531_0]
                            · linarith only [h30561, h4, hlam]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        rcases p30531_3 (m.d 0 2) (by simp) with h30568 | h30568
                        · linarith only [h19744, h30568, hlam]
                        · linarith only [h0, h30568, hlam]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h30189, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h1, h29475, h30178, h30190, hc12, hc24, hlam, hphi, p30531_1]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        rcases p30531_3 (m.d 0 2) (by simp) with h30574 | h30574
                        · linarith only [h30574, hlam, p30531_0]
                        · rcases p30531_3 (m.d 1 2) (by simp) with h30576 | h30576
                          · linarith only [h30182, h30576, hlam]
                          · rcases p30531_3 (m.d 2 3) (by simp) with h30578 | h30578
                            · rcases p30531_3 (m.d 2 4) (by simp) with h30579 | h30579
                              · rcases p30531_3 (m.d 2 5) (by simp) with h30580 | h30580
                                · rcases h4bigk with h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c | h30581c
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h23337, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h19744, hlam, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h23337, hlam, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    rcases p30581_3 (m.d 0 4) (by simp) with h30586 | h30586
                                    · rcases p30581_3 (m.d 1 4) (by simp) with h30587 | h30587
                                      · linarith only [h2, h30587, hlam]
                                      · linarith only [h30188, h30587, hlam]
                                    · linarith only [h30586, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h2, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30180, hlam, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30184, hlam, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p30193_1, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    rcases p30581_3 (m.d 0 4) (by simp) with h30596 | h30596
                                    · linarith only [h19744, h30596, hlam]
                                    · rcases p30581_3 (m.d 1 4) (by simp) with h30598 | h30598
                                      · linarith only [h30180, h30598, hlam]
                                      · rcases p30581_3 (m.d 2 4) (by simp) with h30600 | h30600
                                        · rcases p30581_3 (m.d 3 4) (by simp) with h30601 | h30601
                                          · linarith only [h30189, h30601, hlam]
                                          · linarith only [h23337, h30601, hlam]
                                        · linarith only [h19744, h30600, hlam]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    rcases p30581_3 (m.d 0 4) (by simp) with h30605 | h30605
                                    · linarith only [h19744, h30605, hlam]
                                    · linarith only [h2, h30605, hlam]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h1, h23337, h30178, h30189, hc12, hc23, hlam, hphi, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    rcases p30581_3 (m.d 0 4) (by simp) with h30610 | h30610
                                    · linarith only [h19744, h30610, hlam]
                                    · linarith only [h30177, h30610, hlam]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h2, h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30188, h30189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30581_1]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30189, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    rcases p30581_3 (m.d 0 4) (by simp) with h30617 | h30617
                                    · linarith only [h23337, h30617, hlam]
                                    · linarith only [h30177, h30617, hlam]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30177, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30188, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30191, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [h30192, hlam, p30581_0]
                                  · have p30581_0 := h30581c.1
                                    have p30581_1 := h30581c.2.1
                                    have p30581_2 := h30581c.2.2.1
                                    have p30581_3 := h30581c.2.2.2
                                    linarith only [hlam, p30581_0]
                                · linarith only [h30580, hlam, p30531_0]
                              · linarith only [h19744, h30579, hlam]
                            · linarith only [h30578, h4, hlam]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        rcases p30531_3 (m.d 0 2) (by simp) with h30628 | h30628
                        · linarith only [h22010, h30628, hlam]
                        · linarith only [h0, h30628, hlam]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h30190, hlam, p30531_0]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [h30191, hlam, p30531_1]
                      · have p30531_0 := h30531c.1
                        have p30531_1 := h30531c.2.1
                        have p30531_2 := h30531c.2.2.1
                        have p30531_3 := h30531c.2.2.2
                        linarith only [hlam, p30531_0]
          · linarith only [h30211, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          rcases p30193_3 (m.d 0 1) (by simp) with h30635 | h30635
          · rcases p30193_3 (m.d 1 2) (by simp) with h30636 | h30636
            · linarith only [h0, h30636, hlam]
            · rcases p30193_3 (m.d 1 3) (by simp) with h30638 | h30638
              · linarith only [h1, h30638, hlam]
              · rcases p30193_3 (m.d 1 4) (by simp) with h30640 | h30640
                · linarith only [h2, h30640, hlam]
                · linarith only [h30188, h30640, hlam]
          · linarith only [h30635, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h0, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h30178, hlam, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h30180, hlam, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h30182, hlam, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h1, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h1, h29475, hc12, hc35, hlam, hphi, ht23, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h30184, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h30186, hlam, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h2, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h2, h23337, h30189, hc12, hc23, hlam, hphi, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h2, h23337, h30178, h30189, hc12, hc23, hlam, hphi, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h2, h23337, h30182, h30189, hc12, hc23, hlam, hphi, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h3, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h23337, h3, h30177, h30189, hc12, hc23, hlam, hphi, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h23337, h3, h30177, h30178, h30189, hc12, hc23, hlam, hphi, p30193_1]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [h30188, hlam, p30193_0]
        · have p30193_0 := h30193c.1
          have p30193_1 := h30193c.2.1
          have p30193_2 := h30193c.2.2.1
          have p30193_3 := h30193c.2.2.2
          linarith only [hlam, p30193_0]
      · linarith only [h2, h23337, h30188, h30192, hlam]
    · linarith only [h0, h19744, h2, h23337, h30188, h30189, h30191, hc12, hc23, hlam, hphi]
  · linarith only [h23337, h30189, h30190, hc03, hc35, hlam, hphi]

end R2N4
