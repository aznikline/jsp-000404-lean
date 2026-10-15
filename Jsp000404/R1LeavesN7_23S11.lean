import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S4
import Jsp000404.R1LeavesN7_23S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5932000 in
set_option maxHeartbeats 5932000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s10 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  rcases m.htr 0 3 4 (by decide) (by decide) with h3228 | h3228
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s11 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227 h3228
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6163 | h6163
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6164 | h6164
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6165 | h6165
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6166 | h6166
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6167 | h6167
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6168 | h6168
              · linarith only [h3219, h3228, h6168, hc13, hlam, hphi, u1ehi0]
              · linarith only [h3219, h6168, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h3227, h6167, hlam]
          · linarith only [h0, h3226, h6166, hlam]
        · linarith only [h0, h3225, h6165, hlam]
      · linarith only [h3228, h6163, h6164, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6175 | h6175
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6176 | h6176
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6177 | h6177
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6178 | h6178
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6179 | h6179
              · linarith only [h3219, h3228, h6179, hc13, hlam, hphi, u1ehi0]
              · linarith only [h3219, h6179, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h3227, h6178, hlam]
          · linarith only [h0, h3226, h6177, hlam]
        · linarith only [h0, h3225, h6176, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6185 | h6185
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6186 | h6186
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6187 | h6187
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6188 | h6188
              · linarith only [h3219, h3228, h6188, hc13, hlam, hphi, u1ehi0]
              · linarith only [h3219, h6188, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h0, h3227, h6187, hlam]
          · linarith only [h0, h3226, h6186, hlam]
        · linarith only [h0, h3225, h6185, hlam]

set_option maxHeartbeats 5980000 in
set_option maxHeartbeats 5980000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s9 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  rcases m.htr 0 2 5 (by decide) (by decide) with h3227 | h3227
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s10 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226 h3227
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6194 | h6194
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6195 | h6195
      · linarith only [h3225, h3227, h6195, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6197 | h6197
        · linarith only [h3226, h3227, h6197, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6199 | h6199
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6200 | h6200
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6201 | h6201
              · linarith only [h0, h3227, h6201, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6201, hc25, hlam, hphi, ht12, u1ehi0]
            · linarith only [h3219, h3226, h6199, h6200, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · linarith only [h3225, h3227, h6199, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6206 | h6206
      · linarith only [h3225, h3227, h6206, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6208 | h6208
        · linarith only [h3226, h3227, h6208, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6210 | h6210
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6211 | h6211
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6212 | h6212
              · linarith only [h0, h3227, h6212, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6212, hc25, hlam, hphi, ht12, u1ehi0]
            · linarith only [h3219, h3226, h6210, h6211, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · linarith only [h3225, h3227, h6210, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 6048000 in
set_option maxHeartbeats 6048000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s8 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  rcases m.htr 0 2 4 (by decide) (by decide) with h3226 | h3226
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s9 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225 h3226
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6217 | h6217
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6218 | h6218
      · linarith only [h3225, h3226, h6218, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6220 | h6220
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6221 | h6221
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6222 | h6222
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6223 | h6223
              · linarith only [h3223, h3225, h3226, h6220, h6223, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6223, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h3225, h6222, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · linarith only [h3225, h3226, h6220, h6221, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6228 | h6228
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6229 | h6229
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6230 | h6230
              · linarith only [h0, h3226, h6230, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6230, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h3225, h3226, h6229, hc24, hlam, hphi, ht12, u1ehi0]
          · linarith only [h3226, h6217, h6228, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6235 | h6235
      · linarith only [h3225, h3226, h6235, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6237 | h6237
        · linarith only [h3225, h6217, h6237, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6239 | h6239
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6240 | h6240
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6241 | h6241
              · linarith only [h3219, h3225, h3226, h6241, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6241, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h3225, h6240, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6245 | h6245
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6246 | h6246
              · linarith only [h0, h3226, h6246, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6246, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h3225, h6245, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]

set_option maxHeartbeats 6188000 in
set_option maxHeartbeats 6188000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s7 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  rcases m.htr 0 2 3 (by decide) (by decide) with h3225 | h3225
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s8 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223 h3225
  · rcases m.htr 0 2 4 (by decide) (by decide) with h6250 | h6250
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6251 | h6251
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6252 | h6252
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6253 | h6253
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6254 | h6254
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6255 | h6255
              · linarith only [h0, h3225, h6255, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6255, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6258 | h6258
              · linarith only [h0, h3225, h6258, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6258, hc23, hlam, hphi, ht12, u1ehi0]
          · linarith only [h3225, h6251, h6253, hlam]
        · linarith only [h3225, h6250, h6252, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6263 | h6263
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6264 | h6264
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6265 | h6265
            · linarith only [h6250, h6251, h6265, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6267 | h6267
              · linarith only [h0, h3225, h6267, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6267, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6270 | h6270
            · linarith only [h3225, h6250, h6264, h6270, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6272 | h6272
              · linarith only [h0, h3225, h6272, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6272, hc23, hlam, hphi, ht12, u1ehi0]
        · linarith only [h3225, h6250, h6263, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6276 | h6276
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6277 | h6277
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6278 | h6278
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6279 | h6279
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6280 | h6280
              · linarith only [h0, h3225, h6280, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6280, hc23, hlam, hphi, ht12, u1ehi0]
            · linarith only [h6250, h6276, h6279, hlam]
          · linarith only [h6250, h6276, h6277, h6278, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6285 | h6285
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6286 | h6286
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6287 | h6287
              · linarith only [h0, h3225, h6287, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6287, hc23, hlam, hphi, ht12, u1ehi0]
            · linarith only [h3225, h6276, h6277, h6286, hlam]
          · linarith only [h3225, h6276, h6285, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6292 | h6292
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6293 | h6293
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6294 | h6294
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6295 | h6295
              · linarith only [h0, h3225, h6295, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6295, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6298 | h6298
              · linarith only [h0, h3225, h6298, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6298, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6301 | h6301
            · linarith only [h6292, h6293, h6301, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6303 | h6303
              · linarith only [h0, h3225, h6303, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6303, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6306 | h6306
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6307 | h6307
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6308 | h6308
              · linarith only [h0, h3225, h6308, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6308, hc23, hlam, hphi, ht12, u1ehi0]
            · linarith only [h6292, h6306, h6307, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6312 | h6312
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6313 | h6313
              · linarith only [h0, h3225, h6313, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6313, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6316 | h6316
              · linarith only [h0, h3225, h6316, hc12, hlam, hphi, u1ehi0]
              · linarith only [h0, h6316, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 6192000 in
set_option maxHeartbeats 6192000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  rcases m.htr 0 1 5 (by decide) (by decide) with h3223 | h3223
  · linarith only [h0, h3223, hc12, hlam, hphi, u1ehi4]
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s7 m hb1 hb2 hb4 hb5 h0 h3219 h3221 h3223

set_option maxHeartbeats 6196000 in
set_option maxHeartbeats 6196000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  rcases m.htr 0 1 4 (by decide) (by decide) with h3221 | h3221
  · linarith only [h0, h3221, hc12, hlam, hphi, u1ehi3]
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s6 m hb1 hb2 hb4 hb5 h0 h3219 h3221

set_option maxHeartbeats 6200000 in
set_option maxHeartbeats 6200000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h3219 | h3219
  · linarith only [h0, h3219, hc12, hlam, hphi, u1ehi2]
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s5 m hb1 hb2 hb4 hb5 h0 h3219

set_option maxHeartbeats 12638000 in
set_option maxHeartbeats 12638000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s4 m hb1 hb2 hb4 hb5 h0

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
              · linarith only [h0, h14, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h12, h14, h16, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h12, h14, h18, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h12, h13, h18, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
              · linarith only [h0, h21, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h12, h13, h21, h23, h4, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h13, h25, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h12, h13, h27, hlam]
                    · rcases h2bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi2]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h12, h13, h21, h4, h7, h8, hlam, p29_2]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        rcases p29_3 (m.d 0 2) (by simp) with h33 | h33
                        · rcases p29_3 (m.d 1 2) (by simp) with h34 | h34
                          · linarith only [h0, h34, hlam]
                          · linarith only [h10, h34, hlam]
                        · linarith only [h33, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        rcases p29_3 (m.d 0 2) (by simp) with h38 | h38
                        · rcases p29_3 (m.d 1 2) (by simp) with h39 | h39
                          · linarith only [h0, h39, hlam]
                          · linarith only [h11, h39, hlam]
                        · linarith only [h38, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, hlam, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        rcases p29_3 (m.d 0 2) (by simp) with h45 | h45
                        · rcases p29_3 (m.d 1 2) (by simp) with h46 | h46
                          · rcases p29_3 (m.d 2 3) (by simp) with h47 | h47
                            · linarith only [h47, hlam, p29_0]
                            · rcases p29_3 (m.d 2 4) (by simp) with h49 | h49
                              · linarith only [h10, h49, hlam]
                              · linarith only [h21, h49, hlam]
                          · linarith only [h46, hlam, p29_0]
                        · linarith only [h4, h45, hlam]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi2]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h25, hc01, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi2]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h4, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h9, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h21, hlam, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h23, hlam, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h5, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h10, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h25, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h6, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h11, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi2]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
              · linarith only [h0, h12, h4, h71, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                  · linarith only [h0, h10, h75, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h2, h71, h75, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h10, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h12, h4, h7, h71, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
              · linarith only [h0, h12, h4, h7, h71, h8, h81, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                  · linarith only [h0, h5, h71, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h81, h83, h84, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                  · linarith only [h0, h5, h71, h87, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h10, h4, h7, h71, h89, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases h2bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi2]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h12, h4, h7, h8, h89, h9, hlam, p91_2]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        rcases p91_3 (m.d 0 2) (by simp) with h95 | h95
                        · rcases p91_3 (m.d 1 2) (by simp) with h96 | h96
                          · linarith only [h0, h96, hlam]
                          · linarith only [h10, h96, hlam]
                        · linarith only [h95, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        rcases p91_3 (m.d 0 2) (by simp) with h100 | h100
                        · rcases p91_3 (m.d 1 2) (by simp) with h101 | h101
                          · linarith only [h0, h101, hlam]
                          · linarith only [h101, h11, hlam]
                        · linarith only [h100, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, hlam, p91_1]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        rcases p91_3 (m.d 0 2) (by simp) with h107 | h107
                        · rcases p91_3 (m.d 1 2) (by simp) with h108 | h108
                          · rcases p91_3 (m.d 2 3) (by simp) with h109 | h109
                            · linarith only [h109, hlam, p91_0]
                            · rcases p91_3 (m.d 2 4) (by simp) with h111 | h111
                              · linarith only [h10, h111, hlam]
                              · linarith only [h111, h81, hlam]
                          · linarith only [h108, hlam, p91_0]
                        · linarith only [h107, h4, hlam]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi2]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, h87, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi2]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h4, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h9, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h81, hlam, p91_1]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h83, hlam, p91_1]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h5, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h10, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h87, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h6, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h11, hlam, p91_0]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi2]
                      · have p91_0 := h91c.1
                        have p91_1 := h91c.2.1
                        have p91_2 := h91c.2.2.1
                        have p91_3 := h91c.2.2.2
                        linarith only [hlam, p91_0]
        · linarith only [h0, h10, h11, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
        · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
          · linarith only [h0, h10, h135, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
            · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
              · linarith only [h0, h10, h135, h138, h5, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                · linarith only [h0, h10, h138, h140, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h0, h10, h134, h138, h142, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h10, h134, h140, h142, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h10, h134, h137, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
          · linarith only [h0, h134, h146, h6, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
            · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
              · linarith only [h0, h134, h146, h149, h6, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h151 | h151
                · linarith only [h0, h10, h149, h151, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h154 | h154
                    · rcases h2bigk with h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        rcases p155_3 (m.d 0 2) (by simp) with h157 | h157
                        · rcases p155_3 (m.d 1 2) (by simp) with h158 | h158
                          · linarith only [h0, h158, hlam]
                          · rcases p155_3 (m.d 2 3) (by simp) with h160 | h160
                            · linarith only [h160, h4, hlam]
                            · rcases p155_3 (m.d 2 4) (by simp) with h162 | h162
                              · linarith only [h162, h5, hlam]
                              · linarith only [h10, h162, hlam]
                        · linarith only [h0, h157, hlam]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h134, h149, h153, h4, h7, h9, hlam, p155_2]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h0, h134, h153, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h0, h134, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h0, hlam, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h134, h151, hc23, hc35, hlam, hphi, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h10, hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h134, hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h4, hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h9, hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h149, hlam, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h151, hlam, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h5, hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h0, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        rcases p155_3 (m.d 0 2) (by simp) with h181 | h181
                        · rcases p155_3 (m.d 1 2) (by simp) with h182 | h182
                          · linarith only [h10, h182, hlam]
                          · linarith only [h182, h9, hlam]
                        · linarith only [h181, h4, hlam]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h0, h134, h149, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h6, hlam, p155_0]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h0, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        rcases p155_3 (m.d 0 2) (by simp) with h190 | h190
                        · rcases p155_3 (m.d 1 2) (by simp) with h191 | h191
                          · linarith only [h134, h191, hlam]
                          · linarith only [h191, h9, hlam]
                        · linarith only [h190, h4, hlam]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [h153, hlam, p155_1]
                      · have p155_0 := h155c.1
                        have p155_1 := h155c.2.1
                        have p155_2 := h155c.2.2.1
                        have p155_3 := h155c.2.2.2
                        linarith only [hlam, p155_0]
                    · linarith only [h148, h149, h154, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h10, h148, h153, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
              · linarith only [h10, h199, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                · linarith only [h0, h10, h201, h5, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h0, h10, h148, h199, h203, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h203, h4, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
      · linarith only [h0, h206, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
        · rcases m.htr 1 3 4 (by decide) (by decide) with h209 | h209
          · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
            · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
              · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                · rcases m.htr 2 4 5 (by decide) (by decide) with h213 | h213
                  · linarith only [h0, h206, h208, h211, h213, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h206, h208, h209, h210, h213, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h206, h208, h211, h212, hlam]
              · linarith only [h0, h208, h210, h211, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h206, h208, h210, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
            · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
              · linarith only [h0, h208, h209, h220, h4, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h208, h219, h220, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h206, h208, h219, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
          · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
            · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
              · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                    · linarith only [h1, h224, h229, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2, h225, h229, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h206, h225, h228, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h226, h227, h233, hlam]
                  · linarith only [h206, h225, h233, hlam]
              · linarith only [h224, h226, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
              · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                  · linarith only [h0, h225, h237, h239, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h206, h224, h239, h241, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h206, h239, h4, h7, h8, hlam, p243_2]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h224, h9, hc02, hlam, hphi, ht0b, ht45, ht5b, p243_1, u4ehi3]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        rcases p243_3 (m.d 0 2) (by simp) with h247 | h247
                        · rcases p243_3 (m.d 1 2) (by simp) with h248 | h248
                          · linarith only [h0, h248, hlam]
                          · rcases p243_3 (m.d 2 3) (by simp) with h250 | h250
                            · linarith only [h250, h4, hlam]
                            · linarith only [h237, h250, hlam]
                        · linarith only [h247, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        rcases p243_3 (m.d 0 2) (by simp) with h254 | h254
                        · rcases p243_3 (m.d 1 2) (by simp) with h255 | h255
                          · linarith only [h0, h255, hlam]
                          · rcases p243_3 (m.d 2 3) (by simp) with h257 | h257
                            · linarith only [h257, h4, hlam]
                            · linarith only [h238, h257, hlam]
                        · linarith only [h254, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h0, hlam, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h9, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h206, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h208, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h4, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        rcases p243_3 (m.d 0 2) (by simp) with h267 | h267
                        · rcases p243_3 (m.d 1 2) (by simp) with h268 | h268
                          · linarith only [h268, hlam, p243_0]
                          · rcases p243_3 (m.d 2 3) (by simp) with h270 | h270
                            · rcases p243_3 (m.d 2 4) (by simp) with h271 | h271
                              · linarith only [h237, h271, hlam]
                              · linarith only [h206, h271, hlam]
                            · linarith only [h270, hlam, p243_0]
                        · linarith only [h0, h267, hlam]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h206, hc12, hc23, hlam, hphi, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h0, h208, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h5, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h0, h239, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h237, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h239, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h6, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        rcases p243_3 (m.d 0 2) (by simp) with h285 | h285
                        · rcases p243_3 (m.d 1 2) (by simp) with h286 | h286
                          · linarith only [h286, hlam, p243_0]
                          · rcases p243_3 (m.d 2 3) (by simp) with h288 | h288
                            · rcases p243_3 (m.d 2 4) (by simp) with h289 | h289
                              · linarith only [h239, h289, hlam]
                              · linarith only [h206, h289, hlam]
                            · linarith only [h288, h9, hlam]
                        · linarith only [h0, h285, hlam]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h238, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h0, h206, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p243_1, u4ehi1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h0, h225, h297, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h224, h238, h297, h299, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h224, h238, h299, h4, h7, h8, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h224, h237, h9, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
            · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
              · linarith only [h0, h224, h303, h304, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h306 | h306
                · rcases m.htr 2 4 5 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h308 | h308
                    · linarith only [h0, h304, h306, h308, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h208, h303, h304, h306, h308, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h206, h208, h303, h304, h306, h307, h4, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                    · rcases h2bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h304, h4, h7, h9, hlam, p314_2]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        rcases p314_3 (m.d 0 2) (by simp) with h317 | h317
                        · rcases p314_3 (m.d 1 2) (by simp) with h318 | h318
                          · linarith only [h0, h318, hlam]
                          · rcases p314_3 (m.d 2 3) (by simp) with h320 | h320
                            · linarith only [h320, hlam, p314_0]
                            · rcases p314_3 (m.d 2 4) (by simp) with h322 | h322
                              · linarith only [h322, h5, hlam]
                              · linarith only [h304, h322, hlam]
                        · linarith only [h317, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h0, h206, h303, hc01, hlam, hphi, ht0b, ht45, ht5b, p314_1, u4ehi4]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        rcases p314_3 (m.d 0 2) (by simp) with h327 | h327
                        · rcases p314_3 (m.d 1 2) (by simp) with h328 | h328
                          · linarith only [h0, h328, hlam]
                          · rcases p314_3 (m.d 2 3) (by simp) with h330 | h330
                            · linarith only [h330, h4, hlam]
                            · rcases p314_3 (m.d 2 4) (by simp) with h332 | h332
                              · linarith only [h332, h5, hlam]
                              · linarith only [h312, h332, hlam]
                        · linarith only [h327, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h0, hlam, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h9, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h206, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h208, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h4, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h0, h306, h313, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h304, hlam, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h306, hlam, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h5, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        rcases p314_3 (m.d 0 2) (by simp) with h347 | h347
                        · rcases p314_3 (m.d 1 2) (by simp) with h348 | h348
                          · linarith only [h348, hlam, p314_0]
                          · rcases p314_3 (m.d 2 3) (by simp) with h350 | h350
                            · linarith only [h304, h350, hlam]
                            · linarith only [h350, h9, hlam]
                        · linarith only [h0, h347, hlam]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h0, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h0, h304, h306, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h6, hlam, p314_0]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        rcases p314_3 (m.d 0 2) (by simp) with h358 | h358
                        · rcases p314_3 (m.d 1 2) (by simp) with h359 | h359
                          · linarith only [h359, hlam, p314_0]
                          · rcases p314_3 (m.d 2 3) (by simp) with h361 | h361
                            · linarith only [h306, h361, hlam]
                            · linarith only [h361, h9, hlam]
                        · linarith only [h0, h358, hlam]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h9, hc12, hc25, hlam, hphi, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [h312, hlam, p314_1]
                      · have p314_0 := h314c.1
                        have p314_1 := h314c.2.1
                        have p314_2 := h314c.2.2.1
                        have p314_3 := h314c.2.2.2
                        linarith only [hlam, p314_0]
                    · linarith only [h2, h303, h304, h313, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h206, h303, h312, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
              · rcases m.htr 2 3 5 (by decide) (by decide) with h371 | h371
                · rcases m.htr 2 4 5 (by decide) (by decide) with h372 | h372
                  · linarith only [h0, h303, h372, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h374 | h374
                    · linarith only [h370, h372, h374, hlam]
                    · rcases h2bigk with h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h224, h370, h372, h4, h7, h8, h9, hlam, p376_2]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h0, h224, h370, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p376_1]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        rcases p376_3 (m.d 0 2) (by simp) with h380 | h380
                        · rcases p376_3 (m.d 1 2) (by simp) with h381 | h381
                          · linarith only [h0, h381, hlam]
                          · rcases p376_3 (m.d 2 3) (by simp) with h383 | h383
                            · linarith only [h383, h4, hlam]
                            · linarith only [h370, h383, hlam]
                        · linarith only [h380, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        rcases p376_3 (m.d 0 2) (by simp) with h387 | h387
                        · rcases p376_3 (m.d 1 2) (by simp) with h388 | h388
                          · linarith only [h0, h388, hlam]
                          · rcases p376_3 (m.d 2 3) (by simp) with h390 | h390
                            · linarith only [h390, h4, hlam]
                            · linarith only [h371, h390, hlam]
                        · linarith only [h387, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h0, hlam, p376_1]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h9, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h206, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h208, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h4, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        rcases p376_3 (m.d 0 2) (by simp) with h400 | h400
                        · rcases p376_3 (m.d 1 2) (by simp) with h401 | h401
                          · linarith only [h401, hlam, p376_0]
                          · rcases p376_3 (m.d 2 3) (by simp) with h403 | h403
                            · rcases p376_3 (m.d 2 4) (by simp) with h404 | h404
                              · linarith only [h370, h404, hlam]
                              · linarith only [h206, h404, hlam]
                            · linarith only [h403, hlam, p376_0]
                        · linarith only [h0, h400, hlam]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p376_1, u4ehi2]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h0, h208, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p376_1]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h5, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h0, h372, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p376_1]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h370, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h372, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h6, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        rcases p376_3 (m.d 0 2) (by simp) with h418 | h418
                        · rcases p376_3 (m.d 1 2) (by simp) with h419 | h419
                          · linarith only [h419, hlam, p376_0]
                          · rcases p376_3 (m.d 2 3) (by simp) with h421 | h421
                            · rcases p376_3 (m.d 2 4) (by simp) with h422 | h422
                              · linarith only [h372, h422, hlam]
                              · linarith only [h206, h422, hlam]
                            · linarith only [h421, h9, hlam]
                        · linarith only [h0, h418, hlam]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h371, hlam, p376_0]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p376_1, u4ehi2]
                      · have p376_0 := h376c.1
                        have p376_1 := h376c.2.1
                        have p376_2 := h376c.2.2.1
                        have p376_3 := h376c.2.2.2
                        linarith only [hlam, p376_0]
                · linarith only [h224, h370, h371, h9, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h431 | h431
                · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                  · linarith only [h0, h303, h432, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h370, h431, h432, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h435 | h435
                  · linarith only [h0, h303, h435, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                    · linarith only [h0, h303, h4, h437, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h370, h4, h437, h7, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
    · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
      · rcases m.htr 1 2 5 (by decide) (by decide) with h442 | h442
        · rcases m.htr 1 3 4 (by decide) (by decide) with h443 | h443
          · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
            · linarith only [h2, h444, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
              · linarith only [h0, h440, h446, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                · linarith only [h1, h443, h446, h448, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                  · linarith only [h0, h450, h5, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                    · linarith only [h2, h443, h452, h8, hlam]
                    · rcases h2bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h441, hc01, hlam, hphi, ht0b, ht45, ht5b, p454_1, u4ehi2]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        rcases p454_3 (m.d 0 2) (by simp) with h457 | h457
                        · rcases p454_3 (m.d 1 2) (by simp) with h458 | h458
                          · linarith only [h0, h458, hlam]
                          · linarith only [h440, h458, hlam]
                        · linarith only [h457, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        rcases p454_3 (m.d 0 2) (by simp) with h462 | h462
                        · rcases p454_3 (m.d 1 2) (by simp) with h463 | h463
                          · linarith only [h0, h463, hlam]
                          · linarith only [h441, h463, hlam]
                        · linarith only [h462, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        rcases p454_3 (m.d 0 2) (by simp) with h467 | h467
                        · rcases p454_3 (m.d 1 2) (by simp) with h468 | h468
                          · linarith only [h0, h468, hlam]
                          · linarith only [h442, h468, hlam]
                        · linarith only [h467, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, hlam, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        rcases p454_3 (m.d 0 2) (by simp) with h474 | h474
                        · rcases p454_3 (m.d 1 2) (by simp) with h475 | h475
                          · rcases p454_3 (m.d 2 3) (by simp) with h476 | h476
                            · linarith only [h476, hlam, p454_0]
                            · rcases p454_3 (m.d 2 4) (by simp) with h478 | h478
                              · linarith only [h441, h478, hlam]
                              · linarith only [h446, h478, hlam]
                          · linarith only [h475, hlam, p454_0]
                        · linarith only [h4, h474, hlam]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p454_1, u4ehi2]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h450, hc01, hlam, hphi, ht0b, ht45, ht5b, p454_1, u4ehi2]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h4, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h440, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h446, hlam, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h448, hlam, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h5, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h441, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h5, h8, hc23, hc45, hlam, hphi, ht34, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h450, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h6, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h442, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h442, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h442, hc01, hlam, hphi, ht0b, ht45, ht5b, p454_1, u4ehi2]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
            · linarith only [h443, h500, h7, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h502 | h502
              · linarith only [h0, h440, h443, h502, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h504 | h504
                · rcases m.htr 2 4 5 (by decide) (by decide) with h505 | h505
                  · linarith only [h440, h443, h504, h505, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h440, h443, h504, h505, h7, h8, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h508 | h508
                  · linarith only [h0, h5, h508, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                    · linarith only [h510, h7, h8, hlam]
                    · rcases h2bigk with h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h0, h441, hc01, hlam, hphi, ht0b, ht45, ht5b, p512_1, u4ehi2]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        rcases p512_3 (m.d 0 2) (by simp) with h515 | h515
                        · rcases p512_3 (m.d 1 2) (by simp) with h516 | h516
                          · linarith only [h0, h516, hlam]
                          · linarith only [h440, h516, hlam]
                        · linarith only [h515, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        rcases p512_3 (m.d 0 2) (by simp) with h520 | h520
                        · rcases p512_3 (m.d 1 2) (by simp) with h521 | h521
                          · linarith only [h0, h521, hlam]
                          · linarith only [h441, h521, hlam]
                        · linarith only [h520, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        rcases p512_3 (m.d 0 2) (by simp) with h525 | h525
                        · rcases p512_3 (m.d 1 2) (by simp) with h526 | h526
                          · linarith only [h0, h526, hlam]
                          · linarith only [h442, h526, hlam]
                        · linarith only [h525, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h0, hlam, p512_1]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        rcases p512_3 (m.d 0 2) (by simp) with h532 | h532
                        · rcases p512_3 (m.d 1 2) (by simp) with h533 | h533
                          · rcases p512_3 (m.d 2 3) (by simp) with h534 | h534
                            · linarith only [h534, hlam, p512_0]
                            · rcases p512_3 (m.d 2 4) (by simp) with h536 | h536
                              · linarith only [h441, h536, hlam]
                              · linarith only [h502, h536, hlam]
                          · linarith only [h533, hlam, p512_0]
                        · linarith only [h4, h532, hlam]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p512_1, u4ehi2]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h0, h508, hc01, hlam, hphi, ht0b, ht45, ht5b, p512_1, u4ehi2]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h4, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h440, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h502, hlam, p512_1]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h504, hlam, p512_1]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h5, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h441, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h2, h441, h8, hc23, hc45, hlam, hphi, ht34, p512_1]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h508, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h6, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h442, hlam, p512_0]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h0, h442, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p512_1]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [h0, h442, hc01, hlam, hphi, ht0b, ht45, ht5b, p512_1, u4ehi2]
                      · have p512_0 := h512c.1
                        have p512_1 := h512c.2.1
                        have p512_2 := h512c.2.2.1
                        have p512_3 := h512c.2.2.2
                        linarith only [hlam, p512_0]
        · linarith only [h0, h441, h442, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · linarith only [h440, h441, h5, h8, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
      · linarith only [h0, h4, h440, h560, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h562 | h562
        · rcases m.htr 1 3 4 (by decide) (by decide) with h563 | h563
          · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
            · linarith only [h5, h560, h562, h564, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h5, h560, h562, h564, h8, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
            · linarith only [h440, h562, h563, h567, h7, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h440, h562, h563, h567, h7, h8, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
          · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
            · linarith only [h2, h571, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h573 | h573
              · rcases m.htr 2 3 5 (by decide) (by decide) with h574 | h574
                · rcases m.htr 2 4 5 (by decide) (by decide) with h575 | h575
                  · linarith only [h5, h575, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h577 | h577
                    · linarith only [h5, h560, h570, h577, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        rcases p579_3 (m.d 0 2) (by simp) with h581 | h581
                        · rcases p579_3 (m.d 1 2) (by simp) with h582 | h582
                          · linarith only [h0, h582, hlam]
                          · rcases p579_3 (m.d 2 3) (by simp) with h584 | h584
                            · linarith only [h4, h584, hlam]
                            · linarith only [h440, h584, hlam]
                        · linarith only [h0, h581, hlam]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h440, h570, hc02, hlam, hphi, ht0b, ht45, ht5b, p579_1, u4ehi3]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        rcases p579_3 (m.d 0 2) (by simp) with h589 | h589
                        · rcases p579_3 (m.d 1 2) (by simp) with h590 | h590
                          · linarith only [h0, h590, hlam]
                          · rcases p579_3 (m.d 2 3) (by simp) with h592 | h592
                            · linarith only [h4, h592, hlam]
                            · linarith only [h573, h592, hlam]
                        · linarith only [h589, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        rcases p579_3 (m.d 0 2) (by simp) with h596 | h596
                        · rcases p579_3 (m.d 1 2) (by simp) with h597 | h597
                          · linarith only [h0, h597, hlam]
                          · rcases p579_3 (m.d 2 3) (by simp) with h599 | h599
                            · linarith only [h4, h599, hlam]
                            · linarith only [h574, h599, hlam]
                        · linarith only [h596, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h0, hlam, p579_1]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h440, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h560, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h562, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h4, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        rcases p579_3 (m.d 0 2) (by simp) with h609 | h609
                        · rcases p579_3 (m.d 1 2) (by simp) with h610 | h610
                          · linarith only [h610, hlam, p579_0]
                          · rcases p579_3 (m.d 2 3) (by simp) with h612 | h612
                            · rcases p579_3 (m.d 2 4) (by simp) with h613 | h613
                              · linarith only [h573, h613, hlam]
                              · linarith only [h560, h613, hlam]
                            · linarith only [h612, hlam, p579_0]
                        · linarith only [h0, h609, hlam]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h560, hc12, hc23, hlam, hphi, p579_1]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h0, h4, h560, h575, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p579_1]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h5, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p579_1]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h573, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h575, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h6, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        rcases p579_3 (m.d 0 2) (by simp) with h627 | h627
                        · rcases p579_3 (m.d 1 2) (by simp) with h628 | h628
                          · linarith only [h628, hlam, p579_0]
                          · rcases p579_3 (m.d 2 3) (by simp) with h630 | h630
                            · rcases p579_3 (m.d 2 4) (by simp) with h631 | h631
                              · linarith only [h575, h631, hlam]
                              · linarith only [h560, h631, hlam]
                            · linarith only [h440, h630, hlam]
                        · linarith only [h0, h627, hlam]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h574, hlam, p579_0]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [h0, h560, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p579_1, u4ehi1]
                      · have p579_0 := h579c.1
                        have p579_1 := h579c.2.1
                        have p579_2 := h579c.2.2.1
                        have p579_3 := h579c.2.2.2
                        linarith only [hlam, p579_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h639 | h639
                  · linarith only [h0, h5, h639, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h641 | h641
                    · linarith only [h440, h570, h574, h641, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h440, h570, h574, h641, hc45, hlam, hphi, u4ehi3]
              · linarith only [h440, h570, h573, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h645 | h645
            · linarith only [h2, h645, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h647 | h647
              · rcases m.htr 2 3 5 (by decide) (by decide) with h648 | h648
                · rcases m.htr 2 4 5 (by decide) (by decide) with h649 | h649
                  · linarith only [h5, h649, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h651 | h651
                    · linarith only [h5, h647, h651, h8, hlam]
                    · rcases h2bigk with h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c | h653c
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h4, h440, h570, h648, h651, hlam, p653_2]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h0, h440, h570, h648, h651, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        rcases p653_3 (m.d 0 2) (by simp) with h657 | h657
                        · rcases p653_3 (m.d 1 2) (by simp) with h658 | h658
                          · linarith only [h0, h658, hlam]
                          · rcases p653_3 (m.d 2 3) (by simp) with h660 | h660
                            · linarith only [h4, h660, hlam]
                            · linarith only [h647, h660, hlam]
                        · linarith only [h657, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        rcases p653_3 (m.d 0 2) (by simp) with h664 | h664
                        · rcases p653_3 (m.d 1 2) (by simp) with h665 | h665
                          · linarith only [h0, h665, hlam]
                          · rcases p653_3 (m.d 2 3) (by simp) with h667 | h667
                            · linarith only [h4, h667, hlam]
                            · linarith only [h648, h667, hlam]
                        · linarith only [h664, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h0, hlam, p653_1]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h440, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h560, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h562, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h4, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        rcases p653_3 (m.d 0 2) (by simp) with h677 | h677
                        · rcases p653_3 (m.d 1 2) (by simp) with h678 | h678
                          · linarith only [h678, hlam, p653_0]
                          · rcases p653_3 (m.d 2 3) (by simp) with h680 | h680
                            · rcases p653_3 (m.d 2 4) (by simp) with h681 | h681
                              · linarith only [h647, h681, hlam]
                              · linarith only [h560, h681, hlam]
                            · linarith only [h680, hlam, p653_0]
                        · linarith only [h0, h677, hlam]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h440, h570, h647, hc12, hc23, hlam, hphi, p653_1]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h0, h4, h562, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p653_1]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h5, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p653_1]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h647, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h649, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h6, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        rcases p653_3 (m.d 0 2) (by simp) with h695 | h695
                        · rcases p653_3 (m.d 1 2) (by simp) with h696 | h696
                          · linarith only [h696, hlam, p653_0]
                          · rcases p653_3 (m.d 2 3) (by simp) with h698 | h698
                            · rcases p653_3 (m.d 2 4) (by simp) with h699 | h699
                              · linarith only [h649, h699, hlam]
                              · linarith only [h560, h699, hlam]
                            · linarith only [h440, h698, hlam]
                        · linarith only [h0, h695, hlam]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h648, hlam, p653_0]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p653_1, u4ehi2]
                      · have p653_0 := h653c.1
                        have p653_1 := h653c.2.1
                        have p653_2 := h653c.2.2.1
                        have p653_3 := h653c.2.2.2
                        linarith only [hlam, p653_0]
                · linarith only [h440, h570, h647, h648, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h440, h647, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
