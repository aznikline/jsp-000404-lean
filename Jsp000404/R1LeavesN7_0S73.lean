import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h42074 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h42254 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 3 4 5 (by decide) (by decide) with h42255 | h42255
  · rcases h1bigk with h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c | h42256c
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h0, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h33187, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h36828, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h39227, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      rcases p42256_3 (m.d 0 1) (by simp) with h42262 | h42262
      · linarith only [h42262, hlam, p42256_0]
      · rcases p42256_3 (m.d 1 2) (by simp) with h42264 | h42264
        · rcases p42256_3 (m.d 1 3) (by simp) with h42265 | h42265
          · linarith only [h41033, h42265, hlam]
          · linarith only [h33187, h42265, hlam]
        · linarith only [h42264, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h33187, hc01, hc12, hlam, hphi, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h36828, hc01, hc12, hlam, hphi, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h39227, hc01, hc12, hlam, hphi, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      rcases p42256_3 (m.d 0 1) (by simp) with h42273 | h42273
      · linarith only [h42273, hlam, p42256_0]
      · rcases p42256_3 (m.d 1 2) (by simp) with h42275 | h42275
        · rcases p42256_3 (m.d 1 3) (by simp) with h42276 | h42276
          · rcases p42256_3 (m.d 1 4) (by simp) with h42277 | h42277
            · linarith only [h41036, h42277, hlam]
            · linarith only [h36828, h42277, hlam]
          · linarith only [h42276, hlam, p42256_0]
        · linarith only [h0, h42275, hlam]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h41033, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h36828, hc01, hc13, hlam, hphi, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      rcases p42256_3 (m.d 0 1) (by simp) with h42286 | h42286
      · linarith only [h42286, hlam, p42256_0]
      · rcases p42256_3 (m.d 1 2) (by simp) with h42288 | h42288
        · rcases p42256_3 (m.d 1 3) (by simp) with h42289 | h42289
          · rcases p42256_3 (m.d 1 4) (by simp) with h42290 | h42290
            · rcases p42256_3 (m.d 1 5) (by simp) with h42291 | h42291
              · linarith only [h41038, h42291, hlam]
              · linarith only [h39227, h42291, hlam]
            · linarith only [h42290, hlam, p42256_0]
          · linarith only [h33187, h42289, hlam]
        · linarith only [h0, h42288, hlam]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h41034, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h41036, hlam, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h39227, hc01, hc14, hlam, hphi, p42256_1]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      rcases p42256_3 (m.d 0 1) (by simp) with h42301 | h42301
      · linarith only [h42301, hlam, p42256_0]
      · rcases p42256_3 (m.d 1 2) (by simp) with h42303 | h42303
        · rcases p42256_3 (m.d 1 3) (by simp) with h42304 | h42304
          · rcases p42256_3 (m.d 1 4) (by simp) with h42305 | h42305
            · rcases p42256_3 (m.d 1 5) (by simp) with h42306 | h42306
              · rcases h1emax with h42307 | h42307 | h42307 | h42307 | h42307
                · rcases h2bigk with h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c | h42308c
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h0, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42311 | h42311
                    · rcases p42308_3 (m.d 1 2) (by simp) with h42312 | h42312
                      · rcases p42308_3 (m.d 2 3) (by simp) with h42313 | h42313
                        · linarith only [h42313, hlam, p42308_0]
                        · rcases p42308_3 (m.d 2 4) (by simp) with h42315 | h42315
                          · linarith only [h41028, h42315, hlam]
                          · linarith only [h41039, h42315, hlam]
                      · linarith only [h41033, h42312, hlam]
                    · linarith only [h42311, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42320 | h42320
                    · rcases p42308_3 (m.d 1 2) (by simp) with h42321 | h42321
                      · rcases p42308_3 (m.d 2 3) (by simp) with h42322 | h42322
                        · linarith only [h41027, h42322, hlam]
                        · rcases p42308_3 (m.d 2 4) (by simp) with h42324 | h42324
                          · linarith only [h42324, hlam, p42308_0]
                          · rcases p42308_3 (m.d 2 5) (by simp) with h42326 | h42326
                            · linarith only [h41029, h42326, hlam]
                            · rcases h4bigk with h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c | h42328c
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h36828, hlam, p42328_1]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42331 | h42331
                                · rcases p42328_3 (m.d 1 4) (by simp) with h42332 | h42332
                                  · rcases p42328_3 (m.d 2 4) (by simp) with h42333 | h42333
                                    · linarith only [h41028, h42333, hlam]
                                    · rcases p42328_3 (m.d 3 4) (by simp) with h42335 | h42335
                                      · linarith only [h41030, h42335, hlam]
                                      · linarith only [h41039, h42335, hlam]
                                  · linarith only [h41034, h42332, hlam]
                                · linarith only [h41028, h42331, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42340 | h42340
                                · rcases p42328_3 (m.d 1 4) (by simp) with h42341 | h42341
                                  · rcases p42328_3 (m.d 2 4) (by simp) with h42342 | h42342
                                    · linarith only [h41028, h42342, hlam]
                                    · rcases p42328_3 (m.d 3 4) (by simp) with h42344 | h42344
                                      · linarith only [h41030, h42344, hlam]
                                      · rcases p42328_3 (m.d 4 5) (by simp) with h42346 | h42346
                                        · linarith only [h41032, h42346, hlam]
                                        · rcases h5bigk with h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c | h42348c
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [hlam, p42348_0]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h39227, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            rcases p42348_3 (m.d 0 5) (by simp) with h42351 | h42351
                                            · rcases p42348_3 (m.d 1 5) (by simp) with h42352 | h42352
                                              · rcases p42348_3 (m.d 2 5) (by simp) with h42353 | h42353
                                                · linarith only [h41029, h42353, hlam]
                                                · rcases p42348_3 (m.d 3 5) (by simp) with h42355 | h42355
                                                  · linarith only [h41031, h42355, hlam]
                                                  · linarith only [h42074, h42355, hlam]
                                              · linarith only [h41035, h42352, hlam]
                                            · linarith only [h41029, h42351, hlam]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h42074, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            rcases p42348_3 (m.d 0 5) (by simp) with h42361 | h42361
                                            · rcases p42348_3 (m.d 1 5) (by simp) with h42362 | h42362
                                              · rcases p42348_3 (m.d 2 5) (by simp) with h42363 | h42363
                                                · linarith only [h41029, h42363, hlam]
                                                · linarith only [h42254, h42363, hlam]
                                              · linarith only [h41038, h42362, hlam]
                                            · linarith only [h41032, h42361, hlam]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [hlam, p42348_0]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            rcases p42348_3 (m.d 0 5) (by simp) with h42370 | h42370
                                            · linarith only [h39227, h42370, hlam]
                                            · linarith only [h41029, h42370, hlam]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41033, h41036, h41038, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            rcases p42348_3 (m.d 0 5) (by simp) with h42374 | h42374
                                            · linarith only [h39227, h42374, hlam]
                                            · linarith only [h41032, h42374, hlam]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41029, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41035, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [hlam, p42348_0]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h42074, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h0, h41029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41031, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41037, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h33187, h41031, h41033, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [hlam, p42348_0]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h33187, h41030, h41033, h42255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42328_1, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41032, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h41038, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h42254, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [h42255, hlam, p42348_1]
                                          · have p42348_0 := h42348c.1
                                            have p42348_1 := h42348c.2.1
                                            have p42348_2 := h42348c.2.2.1
                                            have p42348_3 := h42348c.2.2.2
                                            linarith only [hlam, p42348_0]
                                  · linarith only [h41036, h42341, hlam]
                                · linarith only [h41030, h42340, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42394 | h42394
                                · rcases p42328_3 (m.d 1 4) (by simp) with h42395 | h42395
                                  · rcases p42328_3 (m.d 2 4) (by simp) with h42396 | h42396
                                    · linarith only [h41028, h42396, hlam]
                                    · linarith only [h42254, h42396, hlam]
                                  · linarith only [h41038, h42395, hlam]
                                · linarith only [h42394, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42401 | h42401
                                · linarith only [h36828, h42401, hlam]
                                · rcases p42328_3 (m.d 1 4) (by simp) with h42403 | h42403
                                  · rcases p42328_3 (m.d 2 4) (by simp) with h42404 | h42404
                                    · linarith only [h41034, h42404, hlam]
                                    · rcases p42328_3 (m.d 3 4) (by simp) with h42406 | h42406
                                      · linarith only [h41036, h42406, hlam]
                                      · rcases p42328_3 (m.d 4 5) (by simp) with h42408 | h42408
                                        · linarith only [h41038, h42408, hlam]
                                        · rcases h5bigk with h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c | h42410c
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [hlam, p42410_0]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h39227, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41032, h41033, h41036, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42328_1, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h42074, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41032, h41033, h41036, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42328_1, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [hlam, p42410_0]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            rcases p42410_3 (m.d 0 5) (by simp) with h42418 | h42418
                                            · linarith only [h39227, h42418, hlam]
                                            · linarith only [h41029, h42418, hlam]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41033, h41036, h41038, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            rcases p42410_3 (m.d 0 5) (by simp) with h42422 | h42422
                                            · linarith only [h39227, h42422, hlam]
                                            · linarith only [h41032, h42422, hlam]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41029, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41035, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [hlam, p42410_0]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h42074, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h0, h41029, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41031, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41037, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h0, h41027, h41030, h42255, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [hlam, p42410_0]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41030, h41033, h41036, h42255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42328_1, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41032, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h41038, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h42254, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [h42255, hlam, p42410_1]
                                          · have p42410_0 := h42410c.1
                                            have p42410_1 := h42410c.2.1
                                            have p42410_2 := h42410c.2.2.1
                                            have p42410_3 := h42410c.2.2.2
                                            linarith only [hlam, p42410_0]
                                  · linarith only [h36828, h42403, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42442 | h42442
                                · linarith only [h36828, h42442, hlam]
                                · linarith only [h41028, h42442, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42445 | h42445
                                · linarith only [h36828, h42445, hlam]
                                · linarith only [h41030, h42445, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42448 | h42448
                                · linarith only [h36828, h42448, hlam]
                                · linarith only [h41032, h42448, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41028, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41034, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41039, hlam, p42328_1]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42308_1, p42328_1]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41030, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41036, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41027, h41030, hlam, p42308_2, p42328_1]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                rcases p42328_3 (m.d 0 4) (by simp) with h42460 | h42460
                                · rcases p42328_3 (m.d 1 4) (by simp) with h42461 | h42461
                                  · rcases p42328_3 (m.d 2 4) (by simp) with h42462 | h42462
                                    · linarith only [h41039, h42462, hlam]
                                    · linarith only [h42254, h42462, hlam]
                                  · linarith only [h41038, h42461, hlam]
                                · linarith only [h41032, h42460, hlam]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41032, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h41038, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h42254, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [h42255, hlam, p42328_0]
                              · have p42328_0 := h42328c.1
                                have p42328_1 := h42328c.2.1
                                have p42328_2 := h42328c.2.2.1
                                have p42328_3 := h42328c.2.2.2
                                linarith only [hlam, p42328_0]
                      · linarith only [h41034, h42321, hlam]
                    · linarith only [h42320, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42474 | h42474
                    · rcases p42308_3 (m.d 1 2) (by simp) with h42475 | h42475
                      · rcases p42308_3 (m.d 2 3) (by simp) with h42476 | h42476
                        · linarith only [h41027, h42476, hlam]
                        · rcases p42308_3 (m.d 2 4) (by simp) with h42478 | h42478
                          · linarith only [h41028, h42478, hlam]
                          · linarith only [h42254, h42478, hlam]
                      · linarith only [h41035, h42475, hlam]
                    · linarith only [h42474, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41028, h42254, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42308_1]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42485 | h42485
                    · linarith only [h0, h42485, hlam]
                    · linarith only [h41027, h42485, hlam]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42488 | h42488
                    · linarith only [h0, h42488, hlam]
                    · linarith only [h41028, h42488, hlam]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42491 | h42491
                    · linarith only [h0, h42491, hlam]
                    · linarith only [h41029, h42491, hlam]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41027, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41033, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41039, hlam, p42308_1]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h42074, hlam, p42308_1]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41028, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41034, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42501 | h42501
                    · rcases p42308_3 (m.d 1 2) (by simp) with h42502 | h42502
                      · rcases p42308_3 (m.d 2 3) (by simp) with h42503 | h42503
                        · linarith only [h41039, h42503, hlam]
                        · rcases p42308_3 (m.d 2 4) (by simp) with h42505 | h42505
                          · rcases p42308_3 (m.d 2 5) (by simp) with h42506 | h42506
                            · linarith only [h42254, h42506, hlam]
                            · linarith only [h42074, h42506, hlam]
                          · linarith only [h41039, h42505, hlam]
                      · linarith only [h41033, h42502, hlam]
                    · linarith only [h41027, h42501, hlam]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42513 | h42513
                    · rcases p42308_3 (m.d 1 2) (by simp) with h42514 | h42514
                      · rcases p42308_3 (m.d 2 3) (by simp) with h42515 | h42515
                        · linarith only [h41039, h42515, hlam]
                        · rcases p42308_3 (m.d 2 4) (by simp) with h42517 | h42517
                          · rcases p42308_3 (m.d 2 5) (by simp) with h42518 | h42518
                            · linarith only [h42254, h42518, hlam]
                            · rcases h4bigk with h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c | h42520c
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h36828, hlam, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h42074, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42308_1, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41039, h42074, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42308_1, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                rcases p42520_3 (m.d 0 4) (by simp) with h42525 | h42525
                                · rcases p42520_3 (m.d 1 4) (by simp) with h42526 | h42526
                                  · rcases p42520_3 (m.d 2 4) (by simp) with h42527 | h42527
                                    · linarith only [h41028, h42527, hlam]
                                    · linarith only [h42254, h42527, hlam]
                                  · linarith only [h41038, h42526, hlam]
                                · linarith only [h42525, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41028, h41033, h41036, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41033, h41036, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41033, h41036, h41039, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                rcases p42520_3 (m.d 0 4) (by simp) with h42536 | h42536
                                · linarith only [h36828, h42536, hlam]
                                · linarith only [h41032, h42536, hlam]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41028, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41034, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41039, hlam, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                rcases p42520_3 (m.d 0 4) (by simp) with h42543 | h42543
                                · rcases p42520_3 (m.d 1 4) (by simp) with h42544 | h42544
                                  · rcases p42520_3 (m.d 2 4) (by simp) with h42545 | h42545
                                    · rcases p42520_3 (m.d 3 4) (by simp) with h42546 | h42546
                                      · rcases p42520_3 (m.d 4 5) (by simp) with h42547 | h42547
                                        · linarith only [h42547, hlam, p42520_0]
                                        · rcases h5bigk with h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c | h42549c
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [hlam, p42549_0]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h39227, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            rcases p42549_3 (m.d 0 5) (by simp) with h42552 | h42552
                                            · rcases p42549_3 (m.d 1 5) (by simp) with h42553 | h42553
                                              · rcases p42549_3 (m.d 2 5) (by simp) with h42554 | h42554
                                                · linarith only [h41029, h42554, hlam]
                                                · rcases p42549_3 (m.d 3 5) (by simp) with h42556 | h42556
                                                  · linarith only [h41031, h42556, hlam]
                                                  · linarith only [h42074, h42556, hlam]
                                              · linarith only [h41035, h42553, hlam]
                                            · linarith only [h41029, h42552, hlam]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41027, h41030, h41032, h42074, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            rcases p42549_3 (m.d 0 5) (by simp) with h42562 | h42562
                                            · rcases p42549_3 (m.d 1 5) (by simp) with h42563 | h42563
                                              · rcases p42549_3 (m.d 2 5) (by simp) with h42564 | h42564
                                                · linarith only [h41029, h42564, hlam]
                                                · linarith only [h42254, h42564, hlam]
                                              · linarith only [h41038, h42563, hlam]
                                            · linarith only [h41032, h42562, hlam]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h39227, hc01, hc15, hlam, hphi, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [hlam, p42549_0]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            rcases p42549_3 (m.d 0 5) (by simp) with h42571 | h42571
                                            · linarith only [h39227, h42571, hlam]
                                            · linarith only [h41029, h42571, hlam]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41033, h41036, h41038, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            rcases p42549_3 (m.d 0 5) (by simp) with h42575 | h42575
                                            · linarith only [h39227, h42575, hlam]
                                            · linarith only [h41032, h42575, hlam]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41029, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41035, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [hlam, p42549_0]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h42074, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p42308_1, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41031, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41037, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h0, h41027, h41031, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [hlam, p42549_0]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h0, h41027, h41030, h42255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41032, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h41038, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h42254, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [h42255, hlam, p42549_1]
                                          · have p42549_0 := h42549c.1
                                            have p42549_1 := h42549c.2.1
                                            have p42549_2 := h42549c.2.2.1
                                            have p42549_3 := h42549c.2.2.2
                                            linarith only [hlam, p42549_0]
                                      · linarith only [h42255, h42546, hlam]
                                    · linarith only [h42545, hlam, p42520_0]
                                  · linarith only [h41038, h42544, hlam]
                                · linarith only [h41032, h42543, hlam]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41030, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41036, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h0, h41027, h41030, h42254, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42520_1]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                rcases p42520_3 (m.d 0 4) (by simp) with h42601 | h42601
                                · rcases p42520_3 (m.d 1 4) (by simp) with h42602 | h42602
                                  · rcases p42520_3 (m.d 2 4) (by simp) with h42603 | h42603
                                    · linarith only [h41039, h42603, hlam]
                                    · linarith only [h42254, h42603, hlam]
                                  · linarith only [h41038, h42602, hlam]
                                · linarith only [h41032, h42601, hlam]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41032, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h41038, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h42254, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [h42255, hlam, p42520_0]
                              · have p42520_0 := h42520c.1
                                have p42520_1 := h42520c.2.1
                                have p42520_2 := h42520c.2.2.1
                                have p42520_3 := h42520c.2.2.2
                                linarith only [hlam, p42520_0]
                          · linarith only [h42254, h42517, hlam]
                      · linarith only [h41035, h42514, hlam]
                    · linarith only [h41029, h42513, hlam]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41029, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h41035, hlam, p42308_0]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    rcases p42308_3 (m.d 0 2) (by simp) with h42618 | h42618
                    · rcases p42308_3 (m.d 1 2) (by simp) with h42619 | h42619
                      · rcases p42308_3 (m.d 2 3) (by simp) with h42620 | h42620
                        · linarith only [h42074, h42620, hlam]
                        · rcases p42308_3 (m.d 2 4) (by simp) with h42622 | h42622
                          · rcases p42308_3 (m.d 2 5) (by simp) with h42623 | h42623
                            · rcases h4bigk with h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c | h42624c
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h36828, hlam, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h0, h41027, h41030, h42254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h0, h41027, h41030, h42074, h42255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                rcases p42624_3 (m.d 0 4) (by simp) with h42629 | h42629
                                · rcases p42624_3 (m.d 1 4) (by simp) with h42630 | h42630
                                  · rcases p42624_3 (m.d 2 4) (by simp) with h42631 | h42631
                                    · linarith only [h41028, h42631, hlam]
                                    · linarith only [h42254, h42631, hlam]
                                  · linarith only [h41038, h42630, hlam]
                                · linarith only [h42629, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41030, h41033, h41036, h42074, h42255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41033, h41036, h42254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41033, h41036, h42074, h42255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                rcases p42624_3 (m.d 0 4) (by simp) with h42640 | h42640
                                · linarith only [h36828, h42640, hlam]
                                · linarith only [h41032, h42640, hlam]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41028, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41034, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41039, hlam, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                rcases p42624_3 (m.d 0 4) (by simp) with h42647 | h42647
                                · rcases p42624_3 (m.d 1 4) (by simp) with h42648 | h42648
                                  · rcases p42624_3 (m.d 2 4) (by simp) with h42649 | h42649
                                    · rcases p42624_3 (m.d 3 4) (by simp) with h42650 | h42650
                                      · rcases p42624_3 (m.d 4 5) (by simp) with h42651 | h42651
                                        · linarith only [h42651, hlam, p42624_0]
                                        · rcases h5bigk with h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c | h42653c
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [hlam, p42653_0]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h39227, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42308_1, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h39227, h41033, h41036, h41038, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            rcases p42653_3 (m.d 0 5) (by simp) with h42658 | h42658
                                            · rcases p42653_3 (m.d 1 5) (by simp) with h42659 | h42659
                                              · rcases p42653_3 (m.d 2 5) (by simp) with h42660 | h42660
                                                · linarith only [h41029, h42660, hlam]
                                                · linarith only [h42254, h42660, hlam]
                                              · linarith only [h41038, h42659, hlam]
                                            · linarith only [h41032, h42658, hlam]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h39227, h41033, h41036, h41038, hc01, hc12, hlam, hphi, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [hlam, p42653_0]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41033, h41036, h41038, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41033, h41036, h41038, h42074, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            rcases p42653_3 (m.d 0 5) (by simp) with h42669 | h42669
                                            · linarith only [h39227, h42669, hlam]
                                            · linarith only [h41032, h42669, hlam]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41029, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41035, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [hlam, p42653_0]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h42074, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h0, h41028, h42254, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41031, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41037, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h0, h41027, h41030, h42255, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [hlam, p42653_0]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h0, h41027, h41030, h42255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41032, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h41038, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h42254, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [h42255, hlam, p42653_1]
                                          · have p42653_0 := h42653c.1
                                            have p42653_1 := h42653c.2.1
                                            have p42653_2 := h42653c.2.2.1
                                            have p42653_3 := h42653c.2.2.2
                                            linarith only [hlam, p42653_0]
                                      · linarith only [h42255, h42650, hlam]
                                    · linarith only [h42649, hlam, p42624_0]
                                  · linarith only [h41038, h42648, hlam]
                                · linarith only [h41032, h42647, hlam]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41030, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41036, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h0, h41027, h41030, h42254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42308_1, p42624_1]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                rcases p42624_3 (m.d 0 4) (by simp) with h42695 | h42695
                                · rcases p42624_3 (m.d 1 4) (by simp) with h42696 | h42696
                                  · rcases p42624_3 (m.d 2 4) (by simp) with h42697 | h42697
                                    · linarith only [h41039, h42697, hlam]
                                    · linarith only [h42254, h42697, hlam]
                                  · linarith only [h41038, h42696, hlam]
                                · linarith only [h41032, h42695, hlam]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41032, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h41038, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h42254, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [h42255, hlam, p42624_0]
                              · have p42624_0 := h42624c.1
                                have p42624_1 := h42624c.2.1
                                have p42624_2 := h42624c.2.2.1
                                have p42624_3 := h42624c.2.2.2
                                linarith only [hlam, p42624_0]
                            · linarith only [h42074, h42623, hlam]
                          · linarith only [h41039, h42622, hlam]
                      · linarith only [h41033, h42619, hlam]
                    · linarith only [h41027, h42618, hlam]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [h42254, hlam, p42308_1]
                  · have p42308_0 := h42308c.1
                    have p42308_1 := h42308c.2.1
                    have p42308_2 := h42308c.2.2.1
                    have p42308_3 := h42308c.2.2.2
                    linarith only [hlam, p42308_0]
                · linarith only [h0, h42307, hc01, hlam]
                · linarith only [h41036, h41038, h42307, hc01, hlam, p42256_1]
                · linarith only [h41038, h42307, hc01, hlam, p42256_1]
                · linarith only [h42307, hc01, hlam, p42256_1]
              · linarith only [h42306, hlam, p42256_0]
            · linarith only [h36828, h42305, hlam]
          · linarith only [h33187, h42304, hlam]
        · linarith only [h0, h42303, hlam]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h41035, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h41037, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [h41038, hlam, p42256_0]
    · have p42256_0 := h42256c.1
      have p42256_1 := h42256c.2.1
      have p42256_2 := h42256c.2.2.1
      have p42256_3 := h42256c.2.2.2
      linarith only [hlam, p42256_0]
  · linarith only [h41039, h42254, h42255, hlam]

end R2N4
