import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S46
import Jsp000404.R1LeavesN7_0S47

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x0_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h28555 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h28557 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h28558 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h23337 := hg23337
  rcases m.htr 2 4 5 (by decide) (by decide) with h29262 | h29262
  · linarith only [h2, h28544, h28548, h28557, h28558, h29262, hc12, hc35, hlam, hphi, ht23]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h29264 | h29264
    · linarith only [h0, h1, h19744, h28552, h29262, h29264, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases h1bigk with h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c | h29266c
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        rcases p29266_3 (m.d 0 1) (by simp) with h29268 | h29268
        · rcases p29266_3 (m.d 1 2) (by simp) with h29269 | h29269
          · linarith only [h29269, hlam, p29266_0]
          · rcases p29266_3 (m.d 1 3) (by simp) with h29271 | h29271
            · linarith only [h1, h29271, hlam]
            · linarith only [h28546, h29271, hlam]
        · linarith only [h29268, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        rcases p29266_3 (m.d 0 1) (by simp) with h29275 | h29275
        · rcases p29266_3 (m.d 1 2) (by simp) with h29276 | h29276
          · linarith only [h0, h29276, hlam]
          · rcases p29266_3 (m.d 1 3) (by simp) with h29278 | h29278
            · linarith only [h29278, hlam, p29266_0]
            · rcases p29266_3 (m.d 1 4) (by simp) with h29280 | h29280
              · linarith only [h2, h29280, hlam]
              · rcases p29266_3 (m.d 1 5) (by simp) with h29282 | h29282
                · linarith only [h29282, h3, hlam]
                · linarith only [h28553, h29282, hlam]
        · linarith only [h29275, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        rcases p29266_3 (m.d 0 1) (by simp) with h29286 | h29286
        · rcases p29266_3 (m.d 1 2) (by simp) with h29287 | h29287
          · linarith only [h0, h29287, hlam]
          · rcases p29266_3 (m.d 1 3) (by simp) with h29289 | h29289
            · linarith only [h1, h29289, hlam]
            · linarith only [h28552, h29289, hlam]
        · linarith only [h29286, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        rcases p29266_3 (m.d 0 1) (by simp) with h29293 | h29293
        · rcases p29266_3 (m.d 1 2) (by simp) with h29294 | h29294
          · linarith only [h0, h29294, hlam]
          · rcases p29266_3 (m.d 1 3) (by simp) with h29296 | h29296
            · linarith only [h1, h29296, hlam]
            · rcases p29266_3 (m.d 1 4) (by simp) with h29298 | h29298
              · linarith only [h2, h29298, hlam]
              · rcases p29266_3 (m.d 1 5) (by simp) with h29300 | h29300
                · linarith only [h29300, hlam, p29266_0]
                · rcases h1emax with h29302 | h29302 | h29302 | h29302 | h29302
                  · linarith only [h28553, h29302, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29266_1]
                  · rcases h2bigk with h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c | h29304c
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h19744, hc12, hc24, hlam, hphi, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h4, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h19744, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h22010, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h0, hlam, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28546, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28548, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28550, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28558, h29264, hc02, hc45, hlam, hphi, ht23, ht34, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28558, h29264, hc24, hc45, hlam, hphi, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28558, hlam, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h0, h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h28557, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h29262, hlam, p29304_0]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      rcases p29304_3 (m.d 0 2) (by simp) with h29325 | h29325
                      · linarith only [h29325, hlam, p29304_0]
                      · rcases p29304_3 (m.d 1 2) (by simp) with h29327 | h29327
                        · linarith only [h28550, h29327, hlam]
                        · rcases p29304_3 (m.d 2 3) (by simp) with h29329 | h29329
                          · linarith only [h28558, h29329, hlam]
                          · linarith only [h29329, h4, hlam]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      rcases p29304_3 (m.d 0 2) (by simp) with h29332 | h29332
                      · linarith only [h22010, h29332, hlam]
                      · linarith only [h0, h29332, hlam]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h1, h28552, h28558, h29264, h4, hc34, hc45, hlam, hphi, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [h0, h19744, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29304_1]
                    · have p29304_0 := h29304c.1
                      have p29304_1 := h29304c.2.1
                      have p29304_2 := h29304c.2.2.1
                      have p29304_3 := h29304c.2.2.2
                      linarith only [hlam, p29304_0]
                  · rcases h2bigk with h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h19744, h28557, hc12, hc23, hlam, hphi, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h4, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h19744, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h22010, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h0, hlam, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28546, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28548, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28550, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28558, h29264, hc02, hc45, hlam, hphi, ht23, ht34, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28558, h29264, hc24, hc45, hlam, hphi, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28558, hlam, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h0, h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h28557, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h29262, hlam, p29338_0]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      rcases p29338_3 (m.d 0 2) (by simp) with h29359 | h29359
                      · linarith only [h29359, hlam, p29338_0]
                      · rcases p29338_3 (m.d 1 2) (by simp) with h29361 | h29361
                        · linarith only [h28550, h29361, hlam]
                        · rcases p29338_3 (m.d 2 3) (by simp) with h29363 | h29363
                          · linarith only [h28558, h29363, hlam]
                          · linarith only [h29363, h4, hlam]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      rcases p29338_3 (m.d 0 2) (by simp) with h29366 | h29366
                      · linarith only [h22010, h29366, hlam]
                      · linarith only [h0, h29366, hlam]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h0, h28558, h29264, h4, hc12, hc45, hlam, hphi, ht23, ht34, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [h0, h19744, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29338_1]
                    · have p29338_0 := h29338c.1
                      have p29338_1 := h29338c.2.1
                      have p29338_2 := h29338c.2.2.1
                      have p29338_3 := h29338c.2.2.2
                      linarith only [hlam, p29338_0]
                  · rcases h2bigk with h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c | h29372c
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h19744, h28557, hc12, hc23, hlam, hphi, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h4, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h19744, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h22010, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h0, hlam, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28546, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28548, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28550, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28558, h29264, hc02, hc45, hlam, hphi, ht23, ht34, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28558, h29264, hc24, hc45, hlam, hphi, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28558, hlam, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h0, h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h28557, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h29262, hlam, p29372_0]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      rcases p29372_3 (m.d 0 2) (by simp) with h29393 | h29393
                      · linarith only [h29393, hlam, p29372_0]
                      · rcases p29372_3 (m.d 1 2) (by simp) with h29395 | h29395
                        · linarith only [h28550, h29395, hlam]
                        · rcases p29372_3 (m.d 2 3) (by simp) with h29397 | h29397
                          · linarith only [h28558, h29397, hlam]
                          · linarith only [h29397, h4, hlam]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      rcases p29372_3 (m.d 0 2) (by simp) with h29400 | h29400
                      · linarith only [h22010, h29400, hlam]
                      · linarith only [h0, h29400, hlam]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h0, h28558, h29264, h4, hc12, hc45, hlam, hphi, ht23, ht34, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [h0, h19744, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29372_1]
                    · have p29372_0 := h29372c.1
                      have p29372_1 := h29372c.2.1
                      have p29372_2 := h29372c.2.2.1
                      have p29372_3 := h29372c.2.2.2
                      linarith only [hlam, p29372_0]
                  · rcases h2bigk with h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c | h29406c
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h19744, h28557, hc12, hc23, hlam, hphi, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h4, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h19744, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h22010, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h0, hlam, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28546, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28548, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28550, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28558, h29264, hc02, hc45, hlam, hphi, ht23, ht34, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28558, h29264, hc24, hc45, hlam, hphi, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28558, hlam, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h0, h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28557, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h28557, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h29262, hlam, p29406_0]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      rcases p29406_3 (m.d 0 2) (by simp) with h29427 | h29427
                      · linarith only [h29427, hlam, p29406_0]
                      · rcases p29406_3 (m.d 1 2) (by simp) with h29429 | h29429
                        · linarith only [h28550, h29429, hlam]
                        · rcases p29406_3 (m.d 2 3) (by simp) with h29431 | h29431
                          · linarith only [h28558, h29431, hlam]
                          · linarith only [h29431, h4, hlam]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      rcases p29406_3 (m.d 0 2) (by simp) with h29434 | h29434
                      · linarith only [h22010, h29434, hlam]
                      · linarith only [h0, h29434, hlam]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h0, h28558, h29264, h4, hc12, hc45, hlam, hphi, ht23, ht34, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [h0, h19744, h28558, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29406_1]
                    · have p29406_0 := h29406c.1
                      have p29406_1 := h29406c.2.1
                      have p29406_2 := h29406c.2.2.1
                      have p29406_3 := h29406c.2.2.2
                      linarith only [hlam, p29406_0]
        · linarith only [h29293, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h0, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h28546, hlam, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h28548, hlam, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h28550, hlam, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h1, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h1, h23338, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h1, h23338, h28548, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h28553, hlam, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h2, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h2, h23337, h23338, h29264, hc12, hc45, hlam, hphi, ht23, ht34, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h28552, hlam, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h28555, hlam, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h3, hlam, p29266_0]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        rcases p29266_3 (m.d 0 1) (by simp) with h29457 | h29457
        · rcases p29266_3 (m.d 1 2) (by simp) with h29458 | h29458
          · linarith only [h28550, h29458, hlam]
          · rcases p29266_3 (m.d 1 3) (by simp) with h29460 | h29460
            · linarith only [h28553, h29460, hlam]
            · linarith only [h28546, h29460, hlam]
        · linarith only [h0, h29457, hlam]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [h22010, h28552, h28558, h29264, h3, hc34, hc45, hlam, hphi, p29266_1]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        rcases p29266_3 (m.d 0 1) (by simp) with h29465 | h29465
        · rcases p29266_3 (m.d 1 2) (by simp) with h29466 | h29466
          · linarith only [h28550, h29466, hlam]
          · rcases p29266_3 (m.d 1 3) (by simp) with h29468 | h29468
            · linarith only [h28553, h29468, hlam]
            · linarith only [h28552, h29468, hlam]
        · linarith only [h2, h29465, hlam]
      · have p29266_0 := h29266c.1
        have p29266_1 := h29266c.2.1
        have p29266_2 := h29266c.2.2.1
        have p29266_3 := h29266c.2.2.2
        linarith only [hlam, p29266_0]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h28555 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h28557 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h23337 := hg23337
  rcases m.htr 2 3 5 (by decide) (by decide) with h28558 | h28558
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553 h28555 h28557 h28558
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553 h28555 h28557 h28558

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h28555 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h28557 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h23337 := hg23337
  linarith only [h1, h28552, h28557, h4, hlam]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h28555 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h23337 := hg23337
  rcases m.htr 2 3 4 (by decide) (by decide) with h28557 | h28557
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553 h28555 h28557
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553 h28555 h28557

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h23337 := hg23337
  rcases m.htr 1 4 5 (by decide) (by decide) with h28555 | h28555
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553 h28555
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553 h28555

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h23337 := hg23337
  rcases m.htr 1 3 5 (by decide) (by decide) with h28553 | h28553
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552 h28553

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h23337 := hg23337
  linarith only [h23337, h23338, h28552, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h23337 := hg23337
  rcases m.htr 1 3 4 (by decide) (by decide) with h28552 | h28552
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550 h28552

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h23337 := hg23337
  rcases m.htr 1 2 5 (by decide) (by decide) with h28550 | h28550
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548 h28550

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h23337 := hg23337
  rcases m.htr 1 2 4 (by decide) (by decide) with h28548 | h28548
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546 h28548

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h23337 := hg23337
  rcases m.htr 1 2 3 (by decide) (by decide) with h28546 | h28546
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544 h28546

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h23337 := hg23337
  rcases m.htr 0 4 5 (by decide) (by decide) with h28544 | h28544
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338 h28544

set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24 (m : N7Model)
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
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h23337 := hg23337
  rcases m.htr 0 3 5 (by decide) (by decide) with h23338 | h23338
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 h23338

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x0 (m : N7Model)
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
    (h23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010 h23337

end R2N4
