import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S41
import Jsp000404.R1LeavesN7_1S42
import Jsp000404.R1LeavesN7_1S43

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h28287 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  linarith only [h0, h22350, h28287, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 2 3 (by decide) (by decide) with h28287 | h28287
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286 h28287

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28286 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 1 2 3 (by decide) (by decide) with h29241 | h29241
  · rcases m.htr 1 2 4 (by decide) (by decide) with h29242 | h29242
    · rcases m.htr 1 2 5 (by decide) (by decide) with h29243 | h29243
      · rcases m.htr 1 3 4 (by decide) (by decide) with h29244 | h29244
        · rcases m.htr 1 3 5 (by decide) (by decide) with h29245 | h29245
          · rcases m.htr 1 4 5 (by decide) (by decide) with h29246 | h29246
            · rcases m.htr 2 3 4 (by decide) (by decide) with h29247 | h29247
              · linarith only [h22350, h22353, h29247, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h29249 | h29249
                · linarith only [h20697, h22350, h22353, h27842, h28286, h29241, h29244, h29246, h29249, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h29251 | h29251
                  · linarith only [h22351, h28286, h29251, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h29253 | h29253
                    · linarith only [h15532, h22353, h28286, h29241, h29244, h29253, hc01, hc12, hlam, hphi]
                    · linarith only [h15532, h22353, h29241, h29244, h29246, h29253, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h29256 | h29256
              · linarith only [h22350, h22353, h29256, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h29258 | h29258
                · linarith only [h22350, h27842, h29258, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h29260 | h29260
                  · linarith only [h18443, h29246, h29260, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h29262 | h29262
                    · linarith only [h15532, h22353, h28286, h29241, h29244, h29262, hc01, hc12, hlam, hphi]
                    · rcases h0bigk with h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c | h29264c
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h0, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h15532, hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h18443, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h20697, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        rcases p29264_3 (m.d 0 1) (by simp) with h29270 | h29270
                        · linarith only [h0, h29270, hlam]
                        · rcases p29264_3 (m.d 0 2) (by simp) with h29272 | h29272
                          · rcases p29264_3 (m.d 0 3) (by simp) with h29273 | h29273
                            · linarith only [h22350, h29273, hlam]
                            · linarith only [h15532, h29273, hlam]
                          · linarith only [h0, h29272, hlam]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        rcases p29264_3 (m.d 0 1) (by simp) with h29278 | h29278
                        · linarith only [h0, h29278, hlam]
                        · rcases p29264_3 (m.d 0 2) (by simp) with h29280 | h29280
                          · rcases p29264_3 (m.d 0 3) (by simp) with h29281 | h29281
                            · linarith only [h22350, h29281, hlam]
                            · rcases p29264_3 (m.d 0 4) (by simp) with h29283 | h29283
                              · linarith only [h22351, h29283, hlam]
                              · linarith only [h22353, h29283, hlam]
                          · linarith only [h22350, h29280, hlam]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        rcases p29264_3 (m.d 0 1) (by simp) with h29287 | h29287
                        · linarith only [h0, h29287, hlam]
                        · rcases p29264_3 (m.d 0 2) (by simp) with h29289 | h29289
                          · rcases p29264_3 (m.d 0 3) (by simp) with h29290 | h29290
                            · linarith only [h22350, h29290, hlam]
                            · rcases p29264_3 (m.d 0 4) (by simp) with h29292 | h29292
                              · linarith only [h22351, h29292, hlam]
                              · rcases p29264_3 (m.d 0 5) (by simp) with h29294 | h29294
                                · linarith only [h22352, h29294, hlam]
                                · linarith only [h28286, h29294, hlam]
                          · linarith only [h22351, h29289, hlam]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        rcases p29264_3 (m.d 0 1) (by simp) with h29298 | h29298
                        · linarith only [h0, h29298, hlam]
                        · rcases p29264_3 (m.d 0 2) (by simp) with h29300 | h29300
                          · rcases p29264_3 (m.d 0 3) (by simp) with h29301 | h29301
                            · linarith only [h22350, h29301, hlam]
                            · rcases p29264_3 (m.d 0 4) (by simp) with h29303 | h29303
                              · linarith only [h22351, h29303, hlam]
                              · rcases p29264_3 (m.d 0 5) (by simp) with h29305 | h29305
                                · linarith only [h22352, h29305, hlam]
                                · rcases h2bigk with h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c | h29307c
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h0, hlam, p29307_1]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    rcases p29307_3 (m.d 0 2) (by simp) with h29310 | h29310
                                    · rcases p29307_3 (m.d 1 2) (by simp) with h29311 | h29311
                                      · rcases p29307_3 (m.d 2 3) (by simp) with h29312 | h29312
                                        · linarith only [h29312, hlam, p29307_0]
                                        · rcases p29307_3 (m.d 2 4) (by simp) with h29314 | h29314
                                          · linarith only [h22351, h29314, hlam]
                                          · linarith only [h29256, h29314, hlam]
                                      · linarith only [h29241, h29311, hlam]
                                    · linarith only [h29310, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    rcases p29307_3 (m.d 0 2) (by simp) with h29319 | h29319
                                    · rcases p29307_3 (m.d 1 2) (by simp) with h29320 | h29320
                                      · rcases p29307_3 (m.d 2 3) (by simp) with h29321 | h29321
                                        · linarith only [h22350, h29321, hlam]
                                        · rcases p29307_3 (m.d 2 4) (by simp) with h29323 | h29323
                                          · linarith only [h29323, hlam, p29307_0]
                                          · rcases p29307_3 (m.d 2 5) (by simp) with h29325 | h29325
                                            · linarith only [h22352, h29325, hlam]
                                            · linarith only [h29260, h29325, hlam]
                                      · linarith only [h29242, h29320, hlam]
                                    · linarith only [h29319, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    rcases p29307_3 (m.d 0 2) (by simp) with h29330 | h29330
                                    · rcases p29307_3 (m.d 1 2) (by simp) with h29331 | h29331
                                      · rcases p29307_3 (m.d 2 3) (by simp) with h29332 | h29332
                                        · linarith only [h22350, h29332, hlam]
                                        · rcases p29307_3 (m.d 2 4) (by simp) with h29334 | h29334
                                          · linarith only [h22351, h29334, hlam]
                                          · rcases p29307_3 (m.d 2 5) (by simp) with h29336 | h29336
                                            · linarith only [h29336, hlam, p29307_0]
                                            · rcases h3bigk with h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c | h29338c
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h15532, hlam, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h22353, hc23, hc34, hlam, hphi, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h22353, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h27842, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                rcases p29338_3 (m.d 0 3) (by simp) with h29344 | h29344
                                                · linarith only [h15532, h29344, hlam]
                                                · rcases p29338_3 (m.d 1 3) (by simp) with h29346 | h29346
                                                  · rcases p29338_3 (m.d 2 3) (by simp) with h29347 | h29347
                                                    · linarith only [h29241, h29347, hlam]
                                                    · rcases p29338_3 (m.d 3 4) (by simp) with h29349 | h29349
                                                      · linarith only [h29244, h29349, hlam]
                                                      · linarith only [h22353, h29349, hlam]
                                                  · linarith only [h15532, h29346, hlam]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                rcases p29338_3 (m.d 0 3) (by simp) with h29354 | h29354
                                                · linarith only [h15532, h29354, hlam]
                                                · linarith only [h22350, h29354, hlam]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h15532, h22353, h29241, hc01, hc12, hlam, hphi, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h15532, h27842, h29241, hc01, hc12, hlam, hphi, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h22350, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29241, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29256, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29258, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h15532, h29241, h29244, hc01, hc12, hlam, hphi, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29244, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29244, h29246, hc23, hc45, hlam, hphi, ht34, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29262, hlam, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h15532, h29241, h29245, hc01, hc12, hlam, hphi, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h29245, hlam, p29338_0]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                rcases p29338_3 (m.d 0 3) (by simp) with h29371 | h29371
                                                · linarith only [h27842, h29371, hlam]
                                                · linarith only [h22350, h29371, hlam]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [h15532, h22353, h29245, hc01, hc15, hlam, hphi, p29338_1]
                                              · have p29338_0 := h29338c.1
                                                have p29338_1 := h29338c.2.1
                                                have p29338_2 := h29338c.2.2.1
                                                have p29338_3 := h29338c.2.2.2
                                                linarith only [hlam, p29338_0]
                                      · linarith only [h29243, h29331, hlam]
                                    · linarith only [h29330, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h28286, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p29264_1, p29307_1]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    rcases p29307_3 (m.d 0 2) (by simp) with h29380 | h29380
                                    · linarith only [h0, h29380, hlam]
                                    · linarith only [h22350, h29380, hlam]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    rcases p29307_3 (m.d 0 2) (by simp) with h29383 | h29383
                                    · linarith only [h0, h29383, hlam]
                                    · linarith only [h22351, h29383, hlam]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    rcases p29307_3 (m.d 0 2) (by simp) with h29386 | h29386
                                    · linarith only [h0, h29386, hlam]
                                    · linarith only [h22352, h29386, hlam]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h22350, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h29241, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h29256, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h29258, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h22351, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h29242, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h18443, h22351, h29246, hc23, hc45, hlam, hphi, ht34, p29307_1]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h29260, hlam, p29307_1]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h22352, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h29243, hlam, p29307_0]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h0, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29264_1, p29307_1]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [h0, h22352, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p29264_1, p29307_1]
                                  · have p29307_0 := h29307c.1
                                    have p29307_1 := h29307c.2.1
                                    have p29307_2 := h29307c.2.2.1
                                    have p29307_3 := h29307c.2.2.2
                                    linarith only [hlam, p29307_0]
                          · linarith only [h22352, h29300, hlam]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h22353, hc01, hc34, hlam, hphi, ht12, ht23, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h22350, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h22353, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h27842, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h18443, h29246, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h22351, hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h18443, h29246, hc03, hc45, hlam, hphi, ht34, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h28286, hlam, p29264_0]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h27842, h29241, h29245, hc01, hc12, hlam, hphi, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h22352, hlam, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h15532, h27842, h29241, h29245, hc01, hc12, hlam, hphi, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [h18443, h27842, h29241, h29245, hc01, hc12, hlam, hphi, p29264_1]
                      · have p29264_0 := h29264c.1
                        have p29264_1 := h29264c.2.1
                        have p29264_2 := h29264c.2.2.1
                        have p29264_3 := h29264c.2.2.2
                        linarith only [hlam, p29264_0]
          · linarith only [h15532, h22353, h29244, h29245, hc01, hc35, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h29421 | h29421
          · linarith only [h15532, h27842, h29244, h29421, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h29423 | h29423
            · rcases m.htr 2 3 4 (by decide) (by decide) with h29424 | h29424
              · linarith only [h15532, h29244, h29424, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h29426 | h29426
                · linarith only [h0, h20697, h22350, h29421, h29426, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h29428 | h29428
                  · linarith only [h22351, h28286, h29428, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h29430 | h29430
                    · rcases h0bigk with h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c | h29431c
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h0, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h15532, hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h18443, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h20697, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        rcases p29431_3 (m.d 0 1) (by simp) with h29437 | h29437
                        · linarith only [h0, h29437, hlam]
                        · rcases p29431_3 (m.d 0 2) (by simp) with h29439 | h29439
                          · rcases p29431_3 (m.d 0 3) (by simp) with h29440 | h29440
                            · linarith only [h22350, h29440, hlam]
                            · linarith only [h15532, h29440, hlam]
                          · linarith only [h0, h29439, hlam]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        rcases p29431_3 (m.d 0 1) (by simp) with h29445 | h29445
                        · linarith only [h0, h29445, hlam]
                        · rcases p29431_3 (m.d 0 2) (by simp) with h29447 | h29447
                          · rcases p29431_3 (m.d 0 3) (by simp) with h29448 | h29448
                            · linarith only [h22350, h29448, hlam]
                            · rcases p29431_3 (m.d 0 4) (by simp) with h29450 | h29450
                              · linarith only [h22351, h29450, hlam]
                              · linarith only [h22353, h29450, hlam]
                          · linarith only [h22350, h29447, hlam]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        rcases p29431_3 (m.d 0 1) (by simp) with h29454 | h29454
                        · linarith only [h0, h29454, hlam]
                        · rcases p29431_3 (m.d 0 2) (by simp) with h29456 | h29456
                          · rcases p29431_3 (m.d 0 3) (by simp) with h29457 | h29457
                            · linarith only [h22350, h29457, hlam]
                            · rcases p29431_3 (m.d 0 4) (by simp) with h29459 | h29459
                              · linarith only [h22351, h29459, hlam]
                              · rcases p29431_3 (m.d 0 5) (by simp) with h29461 | h29461
                                · linarith only [h22352, h29461, hlam]
                                · linarith only [h28286, h29461, hlam]
                          · linarith only [h22351, h29456, hlam]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        rcases p29431_3 (m.d 0 1) (by simp) with h29465 | h29465
                        · linarith only [h0, h29465, hlam]
                        · rcases p29431_3 (m.d 0 2) (by simp) with h29467 | h29467
                          · rcases p29431_3 (m.d 0 3) (by simp) with h29468 | h29468
                            · linarith only [h22350, h29468, hlam]
                            · rcases p29431_3 (m.d 0 4) (by simp) with h29470 | h29470
                              · linarith only [h22351, h29470, hlam]
                              · rcases p29431_3 (m.d 0 5) (by simp) with h29472 | h29472
                                · linarith only [h22352, h29472, hlam]
                                · rcases h2bigk with h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c | h29474c
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h0, hlam, p29474_1]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    rcases p29474_3 (m.d 0 2) (by simp) with h29477 | h29477
                                    · rcases p29474_3 (m.d 1 2) (by simp) with h29478 | h29478
                                      · rcases p29474_3 (m.d 2 3) (by simp) with h29479 | h29479
                                        · linarith only [h29479, hlam, p29474_0]
                                        · rcases p29474_3 (m.d 2 4) (by simp) with h29481 | h29481
                                          · linarith only [h22351, h29481, hlam]
                                          · linarith only [h29424, h29481, hlam]
                                      · linarith only [h29241, h29478, hlam]
                                    · linarith only [h29477, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    rcases p29474_3 (m.d 0 2) (by simp) with h29486 | h29486
                                    · rcases p29474_3 (m.d 1 2) (by simp) with h29487 | h29487
                                      · rcases p29474_3 (m.d 2 3) (by simp) with h29488 | h29488
                                        · linarith only [h22350, h29488, hlam]
                                        · rcases p29474_3 (m.d 2 4) (by simp) with h29490 | h29490
                                          · linarith only [h29490, hlam, p29474_0]
                                          · rcases p29474_3 (m.d 2 5) (by simp) with h29492 | h29492
                                            · linarith only [h22352, h29492, hlam]
                                            · linarith only [h29428, h29492, hlam]
                                      · linarith only [h29242, h29487, hlam]
                                    · linarith only [h29486, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    rcases p29474_3 (m.d 0 2) (by simp) with h29497 | h29497
                                    · rcases p29474_3 (m.d 1 2) (by simp) with h29498 | h29498
                                      · rcases p29474_3 (m.d 2 3) (by simp) with h29499 | h29499
                                        · linarith only [h22350, h29499, hlam]
                                        · rcases p29474_3 (m.d 2 4) (by simp) with h29501 | h29501
                                          · linarith only [h22351, h29501, hlam]
                                          · rcases p29474_3 (m.d 2 5) (by simp) with h29503 | h29503
                                            · linarith only [h29503, hlam, p29474_0]
                                            · rcases h3bigk with h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c | h29505c
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h15532, hlam, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h22353, h28286, h29423, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h22353, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h27842, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h15532, h29421, hc01, hc35, hlam, hphi, ht12, ht23, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29421, hc23, hc35, hlam, hphi, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29244, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29421, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h22350, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29241, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29424, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29426, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                rcases p29505_3 (m.d 0 3) (by simp) with h29521 | h29521
                                                · linarith only [h29521, hlam, p29505_0]
                                                · rcases p29505_3 (m.d 1 3) (by simp) with h29523 | h29523
                                                  · linarith only [h29244, h29523, hlam]
                                                  · linarith only [h15532, h29523, hlam]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h15532, hc01, hc34, hlam, hphi, ht12, ht23, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                rcases p29505_3 (m.d 0 3) (by simp) with h29527 | h29527
                                                · linarith only [h22353, h29527, hlam]
                                                · linarith only [h22350, h29527, hlam]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h15532, h27842, hc01, hc34, hlam, hphi, ht12, ht23, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                rcases p29505_3 (m.d 0 3) (by simp) with h29532 | h29532
                                                · linarith only [h29532, hlam, p29505_0]
                                                · rcases p29505_3 (m.d 1 3) (by simp) with h29534 | h29534
                                                  · linarith only [h29421, h29534, hlam]
                                                  · linarith only [h15532, h29534, hlam]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h15532, hc01, hc35, hlam, hphi, ht12, ht23, p29505_1]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                rcases p29505_3 (m.d 0 3) (by simp) with h29538 | h29538
                                                · linarith only [h27842, h29538, hlam]
                                                · linarith only [h22350, h29538, hlam]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [h29430, hlam, p29505_0]
                                              · have p29505_0 := h29505c.1
                                                have p29505_1 := h29505c.2.1
                                                have p29505_2 := h29505c.2.2.1
                                                have p29505_3 := h29505c.2.2.2
                                                linarith only [hlam, p29505_0]
                                      · linarith only [h29243, h29498, hlam]
                                    · linarith only [h29497, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p29431_1, p29474_1]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    rcases p29474_3 (m.d 0 2) (by simp) with h29547 | h29547
                                    · linarith only [h0, h29547, hlam]
                                    · linarith only [h22350, h29547, hlam]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    rcases p29474_3 (m.d 0 2) (by simp) with h29550 | h29550
                                    · linarith only [h0, h29550, hlam]
                                    · linarith only [h22351, h29550, hlam]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    rcases p29474_3 (m.d 0 2) (by simp) with h29553 | h29553
                                    · linarith only [h0, h29553, hlam]
                                    · linarith only [h22352, h29553, hlam]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h22350, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h29241, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h29424, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h29426, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h22351, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h29242, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h0, h22351, h28286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29431_1, p29474_1]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h29428, hlam, p29474_1]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h22352, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h29243, hlam, p29474_0]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h0, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29431_1, p29474_1]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [h0, h22352, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p29431_1, p29474_1]
                                  · have p29474_0 := h29474c.1
                                    have p29474_1 := h29474c.2.1
                                    have p29474_2 := h29474c.2.2.1
                                    have p29474_3 := h29474c.2.2.2
                                    linarith only [hlam, p29474_0]
                          · linarith only [h22352, h29467, hlam]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h22353, hc01, hc34, hlam, hphi, ht12, ht23, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h22350, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h22353, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h27842, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h28286, h29244, h29423, hc01, hc34, hlam, hphi, ht12, ht23, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h22351, hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h28286, h29244, h29423, hc03, hc34, hlam, hphi, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h28286, hlam, p29431_0]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h28286, h29244, h29423, hc01, hc34, hlam, hphi, ht12, ht23, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h22352, hlam, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h15532, h28286, h29244, h29423, hc01, hc34, hlam, hphi, ht12, ht23, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [h18443, h28286, h29244, h29423, hc01, hc34, hlam, hphi, ht12, ht23, p29431_1]
                      · have p29431_0 := h29431c.1
                        have p29431_1 := h29431c.2.1
                        have p29431_2 := h29431c.2.2.1
                        have p29431_3 := h29431c.2.2.2
                        linarith only [hlam, p29431_0]
                    · linarith only [h29244, h29423, h29430, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h29588 | h29588
              · linarith only [h22350, h22353, h29588, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h29590 | h29590
                · linarith only [h0, h15532, h22350, h27842, h29590, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h29592 | h29592
                  · linarith only [h15532, h29244, h29423, h29592, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h29594 | h29594
                    · linarith only [h15532, h29244, h29423, h29594, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h15532, h29244, h29594, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h22352, h29243, hlam]
    · linarith only [h0, h22351, h29242, hlam]
  · linarith only [h0, h22350, h29241, hlam]

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h27842 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 0 4 5 (by decide) (by decide) with h28286 | h28286
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842 h28286

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22353 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 0 3 5 (by decide) (by decide) with h27842 | h27842
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353 h27842

set_option maxHeartbeats 14494000 in
set_option maxHeartbeats 14494000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  rcases m.htr 0 3 4 (by decide) (by decide) with h22353 | h22353
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 h22353

set_option maxHeartbeats 14752000 in
set_option maxHeartbeats 14752000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s22 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  rcases m.htr 0 2 5 (by decide) (by decide) with h22352 | h22352
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s23 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351 h22352
  · rcases m.htr 0 3 4 (by decide) (by decide) with h29600 | h29600
    · rcases m.htr 0 3 5 (by decide) (by decide) with h29601 | h29601
      · linarith only [h22350, h22352, h29601, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h29603 | h29603
        · linarith only [h22351, h22352, h29603, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29605 | h29605
          · rcases m.htr 1 2 4 (by decide) (by decide) with h29606 | h29606
            · rcases m.htr 1 2 5 (by decide) (by decide) with h29607 | h29607
              · rcases m.htr 1 3 4 (by decide) (by decide) with h29608 | h29608
                · rcases m.htr 1 3 5 (by decide) (by decide) with h29609 | h29609
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29610 | h29610
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29611 | h29611
                      · linarith only [h22350, h22352, h29607, h29611, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h22350, h22352, h29600, h29607, h29611, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29614 | h29614
                      · linarith only [h22350, h22352, h29607, h29614, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h22350, h22352, h29600, h29607, h29614, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29617 | h29617
                    · linarith only [h18443, h29603, h29608, h29609, h29617, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29619 | h29619
                      · linarith only [h22350, h22352, h29607, h29619, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h22350, h22352, h29600, h29607, h29619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h15532, h22350, h22352, h29600, h29607, h29608, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h29623 | h29623
                · rcases m.htr 1 3 5 (by decide) (by decide) with h29624 | h29624
                  · linarith only [h29600, h29601, h29605, h29607, h29624, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29626 | h29626
                    · linarith only [h18443, h29603, h29606, h29607, h29626, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29628 | h29628
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29629 | h29629
                        · linarith only [h0, h22350, h29607, h29624, h29629, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29631 | h29631
                          · linarith only [h22351, h29603, h29631, hlam]
                          · linarith only [h0, h22350, h29607, h29628, h29631, hc34, hc45, hlam, hphi]
                      · linarith only [h29600, h29601, h29628, hc23, hc35, hlam, hphi]
                · linarith only [h15532, h29600, h29623, hlam]
            · linarith only [h0, h22351, h29606, hlam]
          · linarith only [h0, h22350, h29605, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h29638 | h29638
      · linarith only [h22351, h22352, h29600, h29638, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h29640 | h29640
        · linarith only [h22351, h22352, h29640, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29642 | h29642
          · rcases m.htr 1 2 4 (by decide) (by decide) with h29643 | h29643
            · rcases m.htr 1 2 5 (by decide) (by decide) with h29644 | h29644
              · rcases m.htr 1 3 4 (by decide) (by decide) with h29645 | h29645
                · rcases m.htr 1 3 5 (by decide) (by decide) with h29646 | h29646
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29647 | h29647
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29648 | h29648
                      · linarith only [h22350, h22352, h29600, h29644, h29648, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29650 | h29650
                        · linarith only [h15532, h22351, h22352, h29638, h29644, h29648, h29650, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29652 | h29652
                          · linarith only [h22351, h22352, h29642, h29646, h29650, h29652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h29654 | h29654
                            · linarith only [h22351, h22352, h29648, h29652, h29654, hc23, hc34, hlam, hphi]
                            · linarith only [h15532, h29600, h29642, h29645, h29647, h29654, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29657 | h29657
                      · linarith only [h15532, h22350, h22352, h29600, h29657, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29659 | h29659
                        · linarith only [h22351, h22352, h29638, h29644, h29657, h29659, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29661 | h29661
                          · linarith only [h22351, h22352, h29642, h29646, h29647, h29659, h29661, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h29663 | h29663
                            · linarith only [h29645, h29647, h29663, hlam]
                            · rcases h0bigk with h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c | h29665c
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h0, hlam, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h15532, hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h18443, hlam, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h20697, hlam, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22352, h29642, h29646, h29659, hc01, hc12, hlam, hphi, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h15532, h22352, h29642, h29646, h29659, hc01, hc12, hlam, hphi, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22352, h29642, h29646, h29659, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22352, hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h29600, h29645, hc01, hc14, hlam, hphi, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22350, hlam, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h29600, hlam, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h29638, hlam, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h18443, h22351, h22352, h29642, h29646, h29647, h29657, h29659, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22351, hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22351, h22352, h29642, h29646, h29659, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h29640, hlam, p29665_0]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22352, h29642, h29646, h29659, hc01, hc12, hlam, hphi, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h22351, h22352, h29642, h29646, h29657, h29659, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h15532, h22352, h29642, h29646, h29659, hc01, hc12, hlam, hphi, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [h18443, h22352, h29642, h29646, h29659, hc01, hc12, hlam, hphi, p29665_1]
                              · have p29665_0 := h29665c.1
                                have p29665_1 := h29665c.2.1
                                have p29665_2 := h29665c.2.2.1
                                have p29665_3 := h29665c.2.2.2
                                linarith only [hlam, p29665_0]
                  · linarith only [h15532, h29600, h29645, h29646, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h29692 | h29692
                  · linarith only [h15532, h29638, h29645, h29692, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29694 | h29694
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29695 | h29695
                      · linarith only [h0, h15532, h22350, h29645, h29695, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29697 | h29697
                        · linarith only [h22351, h22352, h29644, h29692, h29695, h29697, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29699 | h29699
                          · linarith only [h15532, h22351, h22352, h29600, h29640, h29644, h29699, hc01, hc12, hlam, hphi]
                          · linarith only [h22351, h22352, h29645, h29694, h29695, h29699, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29702 | h29702
                      · linarith only [h22350, h22352, h29644, h29702, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29704 | h29704
                        · linarith only [h22350, h22352, h29644, h29692, h29704, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29706 | h29706
                          · linarith only [h22351, h22352, h29644, h29694, h29706, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h29708 | h29708
                            · linarith only [h22351, h22352, h29644, h29694, h29702, h29708, hc23, hc34, hlam, hphi]
                            · linarith only [h15532, h29645, h29708, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h29711 | h29711
                · linarith only [h15532, h29600, h29642, h29644, h29711, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h29713 | h29713
                  · linarith only [h15532, h29638, h29643, h29644, h29711, h29713, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29715 | h29715
                    · linarith only [h15532, h29600, h29640, h29643, h29644, h29715, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29717 | h29717
                      · linarith only [h15532, h29711, h29717, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29719 | h29719
                        · linarith only [h0, h22351, h29638, h29644, h29717, h29719, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29721 | h29721
                          · linarith only [h0, h18443, h22351, h29644, h29715, h29719, h29721, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h29723 | h29723
                            · linarith only [h0, h29644, h29721, h29723, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h15532, h29711, h29723, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h22351, h29643, hlam]
          · linarith only [h0, h22350, h29642, hlam]

end R2N4
