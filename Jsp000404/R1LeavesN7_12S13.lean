import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8381 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 0 4 5 (by decide) (by decide) with h10223 | h10223
  · rcases m.htr 1 2 3 (by decide) (by decide) with h10224 | h10224
    · rcases m.htr 1 2 4 (by decide) (by decide) with h10225 | h10225
      · rcases m.htr 1 2 5 (by decide) (by decide) with h10226 | h10226
        · rcases m.htr 1 3 4 (by decide) (by decide) with h10227 | h10227
          · rcases m.htr 1 3 5 (by decide) (by decide) with h10228 | h10228
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10229 | h10229
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10230 | h10230
                · linarith only [h0, h10230, h6794, h8378, h8381, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10232 | h10232
                  · linarith only [h10227, h10232, h8378, h8381, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10234 | h10234
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10235 | h10235
                      · rcases h1bigk with h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c | h10236c
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h0, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h6794, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h7647, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h8170, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          rcases p10236_3 (m.d 0 1) (by simp) with h10242 | h10242
                          · linarith only [h10242, hlam, p10236_0]
                          · rcases p10236_3 (m.d 1 2) (by simp) with h10244 | h10244
                            · rcases p10236_3 (m.d 1 3) (by simp) with h10245 | h10245
                              · linarith only [h10224, h10245, hlam]
                              · linarith only [h10245, h6794, hlam]
                            · linarith only [h10244, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10227, h8381, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10236_1]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10234, h7647, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, p10236_1, u5ehi4]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h8170, hc01, hc12, hlam, hphi, p10236_1]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          rcases p10236_3 (m.d 0 1) (by simp) with h10253 | h10253
                          · linarith only [h10253, hlam, p10236_0]
                          · rcases p10236_3 (m.d 1 2) (by simp) with h10255 | h10255
                            · rcases p10236_3 (m.d 1 3) (by simp) with h10256 | h10256
                              · rcases p10236_3 (m.d 1 4) (by simp) with h10257 | h10257
                                · linarith only [h10227, h10257, hlam]
                                · linarith only [h10257, h7647, hlam]
                              · linarith only [h10256, hlam, p10236_0]
                            · linarith only [h0, h10255, hlam]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10224, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10227, h10234, h8379, h8381, hc13, hlam, hphi, ht01, ht0b, ht5b, p10236_1, u5ehi4]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10224, h8170, hc01, hc12, hlam, hphi, p10236_1]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          rcases p10236_3 (m.d 0 1) (by simp) with h10266 | h10266
                          · linarith only [h10266, hlam, p10236_0]
                          · rcases p10236_3 (m.d 1 2) (by simp) with h10268 | h10268
                            · rcases p10236_3 (m.d 1 3) (by simp) with h10269 | h10269
                              · rcases p10236_3 (m.d 1 4) (by simp) with h10270 | h10270
                                · rcases p10236_3 (m.d 1 5) (by simp) with h10271 | h10271
                                  · linarith only [h10229, h10271, hlam]
                                  · linarith only [h10271, h8170, hlam]
                                · linarith only [h10270, hlam, p10236_0]
                              · linarith only [h10269, h6794, hlam]
                            · linarith only [h0, h10268, hlam]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10225, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10227, hlam, p10236_1]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h8170, hc01, hc14, hlam, hphi, p10236_1]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          rcases p10236_3 (m.d 0 1) (by simp) with h10281 | h10281
                          · linarith only [h10281, hlam, p10236_0]
                          · rcases p10236_3 (m.d 1 2) (by simp) with h10283 | h10283
                            · rcases p10236_3 (m.d 1 3) (by simp) with h10284 | h10284
                              · rcases p10236_3 (m.d 1 4) (by simp) with h10285 | h10285
                                · rcases p10236_3 (m.d 1 5) (by simp) with h10286 | h10286
                                  · rcases h2bigk with h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c | h10287c
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h0, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      rcases p10287_3 (m.d 0 2) (by simp) with h10290 | h10290
                                      · rcases p10287_3 (m.d 1 2) (by simp) with h10291 | h10291
                                        · rcases p10287_3 (m.d 2 3) (by simp) with h10292 | h10292
                                          · linarith only [h10292, hlam, p10287_0]
                                          · rcases p10287_3 (m.d 2 4) (by simp) with h10294 | h10294
                                            · linarith only [h10294, h8379, hlam]
                                            · linarith only [h10230, h10294, hlam]
                                        · linarith only [h10224, h10291, hlam]
                                      · linarith only [h10290, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10234, hc02, hlam, hphi, ht0b, ht5b, p10287_1, u5ehi4]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      rcases p10287_3 (m.d 0 2) (by simp) with h10300 | h10300
                                      · rcases p10287_3 (m.d 1 2) (by simp) with h10301 | h10301
                                        · rcases p10287_3 (m.d 2 3) (by simp) with h10302 | h10302
                                          · linarith only [h10302, h8378, hlam]
                                          · rcases p10287_3 (m.d 2 4) (by simp) with h10304 | h10304
                                            · linarith only [h10304, h8379, hlam]
                                            · linarith only [h10234, h10304, hlam]
                                        · linarith only [h10226, h10301, hlam]
                                      · linarith only [h10300, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10234, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, p10287_1, u5ehi4]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      rcases p10287_3 (m.d 0 2) (by simp) with h10311 | h10311
                                      · linarith only [h0, h10311, hlam]
                                      · linarith only [h10311, h8378, hlam]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10234, hc12, hlam, hphi, ht01, ht0b, ht5b, p10287_1, u5ehi4]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      rcases p10287_3 (m.d 0 2) (by simp) with h10315 | h10315
                                      · linarith only [h0, h10315, hlam]
                                      · linarith only [h10315, h8380, hlam]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h8378, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10224, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10230, hlam, p10287_1]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10232, hlam, p10287_1]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h8379, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10225, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      rcases p10287_3 (m.d 0 2) (by simp) with h10325 | h10325
                                      · rcases p10287_3 (m.d 1 2) (by simp) with h10326 | h10326
                                        · rcases p10287_3 (m.d 2 3) (by simp) with h10327 | h10327
                                          · linarith only [h10230, h10327, hlam]
                                          · rcases p10287_3 (m.d 2 4) (by simp) with h10329 | h10329
                                            · rcases p10287_3 (m.d 2 5) (by simp) with h10330 | h10330
                                              · linarith only [h10234, h10330, hlam]
                                              · linarith only [h10232, h10330, hlam]
                                            · linarith only [h10230, h10329, hlam]
                                        · linarith only [h10224, h10326, hlam]
                                      · linarith only [h10325, h8378, hlam]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h8379, hc02, hlam, hphi, ht0b, ht5b, p10287_1, u5ehi2]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h8380, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10226, hlam, p10287_0]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      rcases p10287_3 (m.d 0 2) (by simp) with h10340 | h10340
                                      · rcases p10287_3 (m.d 1 2) (by simp) with h10341 | h10341
                                        · rcases p10287_3 (m.d 2 3) (by simp) with h10342 | h10342
                                          · linarith only [h10232, h10342, hlam]
                                          · rcases p10287_3 (m.d 2 4) (by simp) with h10344 | h10344
                                            · rcases p10287_3 (m.d 2 5) (by simp) with h10345 | h10345
                                              · rcases h4bigk with h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h7647, hlam, p10346_1]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10224, h10227, h10234, h8381, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1, u5ehi4]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h8381, hlam, p10346_1]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10224, h10227, h8381, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1, u5ehi4]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10223, h10224, h10227, h8380, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10287_1, p10346_1]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10225, h10234, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1, u5ehi4]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10223, h10224, h10227, h8380, h8381, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10287_1, p10346_1]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  rcases p10346_3 (m.d 0 4) (by simp) with h10356 | h10356
                                                  · linarith only [h10356, h7647, hlam]
                                                  · linarith only [h10223, h10356, hlam]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h8379, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10225, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10230, hlam, p10346_1]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h0, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1, u5ehi4]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10223, h8380, hc23, hc34, hlam, hphi, p10287_1, p10346_1]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10227, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10224, h10227, h10234, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1, u5ehi4]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10224, h10227, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1, u5ehi4]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10223, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10229, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10234, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [h10235, hlam, p10346_0]
                                                · have p10346_0 := h10346c.1
                                                  have p10346_1 := h10346c.2.1
                                                  have p10346_2 := h10346c.2.2.1
                                                  have p10346_3 := h10346c.2.2.2
                                                  linarith only [hlam, p10346_0]
                                              · linarith only [h10232, h10345, hlam]
                                            · linarith only [h10230, h10344, hlam]
                                        · linarith only [h10224, h10341, hlam]
                                      · linarith only [h10340, h8378, hlam]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [h10234, hlam, p10287_1]
                                    · have p10287_0 := h10287c.1
                                      have p10287_1 := h10287c.2.1
                                      have p10287_2 := h10287c.2.2.1
                                      have p10287_3 := h10287c.2.2.2
                                      linarith only [hlam, p10287_0]
                                  · linarith only [h10286, hlam, p10236_0]
                                · linarith only [h10285, h7647, hlam]
                              · linarith only [h10284, h6794, hlam]
                            · linarith only [h0, h10283, hlam]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10226, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10228, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [h10229, hlam, p10236_0]
                        · have p10236_0 := h10236c.1
                          have p10236_1 := h10236c.2.1
                          have p10236_2 := h10236c.2.2.1
                          have p10236_3 := h10236c.2.2.2
                          linarith only [hlam, p10236_0]
                      · linarith only [h10223, h10235, h8381, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10389 | h10389
                      · rcases h1bigk with h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c | h10390c
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h0, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h6794, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h7647, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h8170, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          rcases p10390_3 (m.d 0 1) (by simp) with h10396 | h10396
                          · linarith only [h10396, hlam, p10390_0]
                          · rcases p10390_3 (m.d 1 2) (by simp) with h10398 | h10398
                            · rcases p10390_3 (m.d 1 3) (by simp) with h10399 | h10399
                              · linarith only [h10224, h10399, hlam]
                              · linarith only [h10399, h6794, hlam]
                            · linarith only [h10398, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h6794, hc01, hc12, hlam, hphi, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10223, h10230, h10234, h7647, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h8170, hc01, hc12, hlam, hphi, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          rcases p10390_3 (m.d 0 1) (by simp) with h10407 | h10407
                          · linarith only [h10407, hlam, p10390_0]
                          · rcases p10390_3 (m.d 1 2) (by simp) with h10409 | h10409
                            · rcases p10390_3 (m.d 1 3) (by simp) with h10410 | h10410
                              · rcases p10390_3 (m.d 1 4) (by simp) with h10411 | h10411
                                · linarith only [h10227, h10411, hlam]
                                · linarith only [h10411, h7647, hlam]
                              · linarith only [h10410, hlam, p10390_0]
                            · linarith only [h0, h10409, hlam]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10224, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10223, h10227, h10230, h10234, h8381, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10224, h8170, hc01, hc12, hlam, hphi, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          rcases p10390_3 (m.d 0 1) (by simp) with h10420 | h10420
                          · linarith only [h10420, hlam, p10390_0]
                          · rcases p10390_3 (m.d 1 2) (by simp) with h10422 | h10422
                            · rcases p10390_3 (m.d 1 3) (by simp) with h10423 | h10423
                              · rcases p10390_3 (m.d 1 4) (by simp) with h10424 | h10424
                                · rcases p10390_3 (m.d 1 5) (by simp) with h10425 | h10425
                                  · linarith only [h10229, h10425, hlam]
                                  · linarith only [h10425, h8170, hlam]
                                · linarith only [h10424, hlam, p10390_0]
                              · linarith only [h10423, h6794, hlam]
                            · linarith only [h0, h10422, hlam]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10225, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10227, hlam, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h8170, hc01, hc14, hlam, hphi, p10390_1]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          rcases p10390_3 (m.d 0 1) (by simp) with h10435 | h10435
                          · linarith only [h10435, hlam, p10390_0]
                          · rcases p10390_3 (m.d 1 2) (by simp) with h10437 | h10437
                            · rcases p10390_3 (m.d 1 3) (by simp) with h10438 | h10438
                              · rcases p10390_3 (m.d 1 4) (by simp) with h10439 | h10439
                                · rcases p10390_3 (m.d 1 5) (by simp) with h10440 | h10440
                                  · rcases h2bigk with h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c | h10441c
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h0, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      rcases p10441_3 (m.d 0 2) (by simp) with h10444 | h10444
                                      · rcases p10441_3 (m.d 1 2) (by simp) with h10445 | h10445
                                        · rcases p10441_3 (m.d 2 3) (by simp) with h10446 | h10446
                                          · linarith only [h10446, hlam, p10441_0]
                                          · rcases p10441_3 (m.d 2 4) (by simp) with h10448 | h10448
                                            · linarith only [h10448, h8379, hlam]
                                            · linarith only [h10230, h10448, hlam]
                                        · linarith only [h10224, h10445, hlam]
                                      · linarith only [h10444, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      rcases p10441_3 (m.d 0 2) (by simp) with h10453 | h10453
                                      · rcases p10441_3 (m.d 1 2) (by simp) with h10454 | h10454
                                        · rcases p10441_3 (m.d 2 3) (by simp) with h10455 | h10455
                                          · linarith only [h10455, h8378, hlam]
                                          · rcases p10441_3 (m.d 2 4) (by simp) with h10457 | h10457
                                            · linarith only [h10457, hlam, p10441_0]
                                            · rcases p10441_3 (m.d 2 5) (by simp) with h10459 | h10459
                                              · linarith only [h10459, h8380, hlam]
                                              · linarith only [h10234, h10459, hlam]
                                        · linarith only [h10225, h10454, hlam]
                                      · linarith only [h10453, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      rcases p10441_3 (m.d 0 2) (by simp) with h10464 | h10464
                                      · rcases p10441_3 (m.d 1 2) (by simp) with h10465 | h10465
                                        · rcases p10441_3 (m.d 2 3) (by simp) with h10466 | h10466
                                          · linarith only [h10466, h8378, hlam]
                                          · rcases p10441_3 (m.d 2 4) (by simp) with h10468 | h10468
                                            · linarith only [h10468, h8379, hlam]
                                            · rcases p10441_3 (m.d 2 5) (by simp) with h10470 | h10470
                                              · linarith only [h10470, hlam, p10441_0]
                                              · rcases h4bigk with h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c | h10472c
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h7647, hlam, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  rcases p10472_3 (m.d 0 4) (by simp) with h10475 | h10475
                                                  · rcases p10472_3 (m.d 1 4) (by simp) with h10476 | h10476
                                                    · rcases p10472_3 (m.d 2 4) (by simp) with h10477 | h10477
                                                      · linarith only [h10477, h8379, hlam]
                                                      · rcases p10472_3 (m.d 3 4) (by simp) with h10479 | h10479
                                                        · rcases p10472_3 (m.d 4 5) (by simp) with h10480 | h10480
                                                          · linarith only [h10223, h10480, hlam]
                                                          · linarith only [h10234, h10480, hlam]
                                                        · linarith only [h10230, h10479, hlam]
                                                    · linarith only [h10225, h10476, hlam]
                                                  · linarith only [h10475, h8379, hlam]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h8381, hlam, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10230, h10234, h8381, hc23, hc34, hlam, hphi, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10223, h10224, h10227, h10230, h10234, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  rcases p10472_3 (m.d 0 4) (by simp) with h10490 | h10490
                                                  · linarith only [h10490, h7647, hlam]
                                                  · linarith only [h10490, h8379, hlam]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h6794, h8381, hc01, hc14, hlam, hphi, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  rcases p10472_3 (m.d 0 4) (by simp) with h10494 | h10494
                                                  · linarith only [h10494, h7647, hlam]
                                                  · linarith only [h10223, h10494, hlam]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h8379, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10225, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10230, hlam, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10234, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10223, h10230, h10234, hc23, hc34, hlam, hphi, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10227, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  rcases p10472_3 (m.d 0 4) (by simp) with h10504 | h10504
                                                  · linarith only [h10504, h8381, hlam]
                                                  · linarith only [h10504, h8379, hlam]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10224, h10227, h10230, h10234, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10223, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10229, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10223, h10224, h10227, h10230, h8381, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10472_1]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [h10389, hlam, p10472_0]
                                                · have p10472_0 := h10472c.1
                                                  have p10472_1 := h10472c.2.1
                                                  have p10472_2 := h10472c.2.2.1
                                                  have p10472_3 := h10472c.2.2.2
                                                  linarith only [hlam, p10472_0]
                                        · linarith only [h10226, h10465, hlam]
                                      · linarith only [h10464, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10223, h8379, hc12, hlam, hphi, ht01, ht0b, ht5b, p10441_1, u5ehi4]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10223, h10224, h10227, h10230, h10234, h8381, hlam, p10441_2]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10223, h10224, h10227, h10234, h8381, hlam, p10441_2]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      rcases p10441_3 (m.d 0 2) (by simp) with h10520 | h10520
                                      · linarith only [h0, h10520, hlam]
                                      · linarith only [h10520, h8380, hlam]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h8378, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10224, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10230, hlam, p10441_1]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10232, hlam, p10441_1]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h8379, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10225, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10223, h10224, h10227, h10234, h8381, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10441_1]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10234, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h8380, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10226, hlam, p10441_0]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10223, h10224, h10227, h10234, h8381, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10441_1]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [h10223, h10224, h10227, h10234, h8381, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10441_1]
                                    · have p10441_0 := h10441c.1
                                      have p10441_1 := h10441c.2.1
                                      have p10441_2 := h10441c.2.2.1
                                      have p10441_3 := h10441c.2.2.2
                                      linarith only [hlam, p10441_0]
                                  · linarith only [h10440, hlam, p10390_0]
                                · linarith only [h10439, h7647, hlam]
                              · linarith only [h10438, h6794, hlam]
                            · linarith only [h0, h10437, hlam]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10226, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10228, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [h10229, hlam, p10390_0]
                        · have p10390_0 := h10390c.1
                          have p10390_1 := h10390c.2.1
                          have p10390_2 := h10390c.2.2.1
                          have p10390_3 := h10390c.2.2.2
                          linarith only [hlam, p10390_0]
                      · linarith only [h10223, h10389, h8381, hlam]
              · linarith only [h10223, h10224, h10227, h10229, h7647, h8381, hc01, hc12, hlam, hphi]
            · linarith only [h10223, h10227, h10228, h8381, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h10549 | h10549
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10550 | h10550
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10551 | h10551
                · linarith only [h10227, h10549, h10551, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10553 | h10553
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10554 | h10554
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10555 | h10555
                      · rcases h1bigk with h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h0, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h6794, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h7647, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h8170, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          rcases p10556_3 (m.d 0 1) (by simp) with h10562 | h10562
                          · linarith only [h10562, hlam, p10556_0]
                          · rcases p10556_3 (m.d 1 2) (by simp) with h10564 | h10564
                            · rcases p10556_3 (m.d 1 3) (by simp) with h10565 | h10565
                              · linarith only [h10224, h10565, hlam]
                              · linarith only [h10565, h6794, hlam]
                            · linarith only [h10564, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10553, h10555, h6794, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, p10556_1, u5ehi4]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10227, h10553, h10555, h6794, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, p10556_1, u5ehi4]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h8170, hc01, hc12, hlam, hphi, p10556_1]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10227, hc01, hc34, hlam, hphi, ht12, ht23, p10556_1]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10224, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10227, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10227, h8170, hc01, hc34, hlam, hphi, ht12, ht23, p10556_1]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          rcases p10556_3 (m.d 0 1) (by simp) with h10578 | h10578
                          · linarith only [h10578, hlam, p10556_0]
                          · rcases p10556_3 (m.d 1 2) (by simp) with h10580 | h10580
                            · rcases p10556_3 (m.d 1 3) (by simp) with h10581 | h10581
                              · linarith only [h10227, h10581, hlam]
                              · linarith only [h10581, h6794, hlam]
                            · linarith only [h0, h10580, hlam]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10225, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h6794, hc01, hc14, hlam, hphi, p10556_1]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10227, h8170, hc01, hc34, hlam, hphi, ht12, ht23, p10556_1]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10227, h10549, hc01, hc34, hlam, hphi, ht12, ht23, p10556_1]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10226, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10549, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [h10550, hlam, p10556_0]
                        · have p10556_0 := h10556c.1
                          have p10556_1 := h10556c.2.1
                          have p10556_2 := h10556c.2.2.1
                          have p10556_3 := h10556c.2.2.2
                          linarith only [hlam, p10556_0]
                      · linarith only [h10227, h10555, h6794, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h10223, h10551, h10553, h10554, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h10227, h10549, h10553, hc23, hc34, hlam, hphi]
              · linarith only [h10223, h10550, h7647, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10598 | h10598
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10599 | h10599
                · linarith only [h10227, h10599, h6794, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10601 | h10601
                  · linarith only [h10549, h10601, h6794, h8378, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10603 | h10603
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10604 | h10604
                      · rcases h1bigk with h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h0, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h6794, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h7647, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h8170, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          rcases p10605_3 (m.d 0 1) (by simp) with h10611 | h10611
                          · linarith only [h10611, hlam, p10605_0]
                          · rcases p10605_3 (m.d 1 2) (by simp) with h10613 | h10613
                            · rcases p10605_3 (m.d 1 3) (by simp) with h10614 | h10614
                              · linarith only [h10224, h10614, hlam]
                              · linarith only [h10614, h6794, hlam]
                            · linarith only [h10613, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h6794, hc01, hc12, hlam, hphi, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h7647, hc01, hc12, hlam, hphi, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h8170, hc01, hc12, hlam, hphi, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10549, h10604, hc01, hc34, hlam, hphi, ht12, ht23, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10224, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10227, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10549, hlam, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          rcases p10605_3 (m.d 0 1) (by simp) with h10627 | h10627
                          · linarith only [h10627, hlam, p10605_0]
                          · rcases p10605_3 (m.d 1 2) (by simp) with h10629 | h10629
                            · rcases p10605_3 (m.d 1 3) (by simp) with h10630 | h10630
                              · linarith only [h10227, h10630, hlam]
                              · linarith only [h10630, h6794, hlam]
                            · linarith only [h0, h10629, hlam]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10225, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h6794, hc01, hc14, hlam, hphi, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10227, h10549, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          rcases p10605_3 (m.d 0 1) (by simp) with h10638 | h10638
                          · linarith only [h10638, hlam, p10605_0]
                          · rcases p10605_3 (m.d 1 2) (by simp) with h10640 | h10640
                            · rcases p10605_3 (m.d 1 3) (by simp) with h10641 | h10641
                              · linarith only [h10549, h10641, hlam]
                              · linarith only [h10641, h6794, hlam]
                            · linarith only [h0, h10640, hlam]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10226, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h6794, hc01, hc15, hlam, hphi, p10605_1]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [h10598, hlam, p10605_0]
                        · have p10605_0 := h10605c.1
                          have p10605_1 := h10605c.2.1
                          have p10605_2 := h10605c.2.2.1
                          have p10605_3 := h10605c.2.2.2
                          linarith only [hlam, p10605_0]
                      · linarith only [h10227, h10603, h10604, h7647, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10650 | h10650
                      · rcases h1bigk with h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c | h10651c
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h0, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h6794, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h7647, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h8170, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          rcases p10651_3 (m.d 0 1) (by simp) with h10657 | h10657
                          · linarith only [h10657, hlam, p10651_0]
                          · rcases p10651_3 (m.d 1 2) (by simp) with h10659 | h10659
                            · rcases p10651_3 (m.d 1 3) (by simp) with h10660 | h10660
                              · linarith only [h10224, h10660, hlam]
                              · linarith only [h10660, h6794, hlam]
                            · linarith only [h10659, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h6794, hc01, hc12, hlam, hphi, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h7647, hc01, hc12, hlam, hphi, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h8170, hc01, hc12, hlam, hphi, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10549, h10650, hc01, hc34, hlam, hphi, ht12, ht23, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10224, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10227, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10549, hlam, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          rcases p10651_3 (m.d 0 1) (by simp) with h10673 | h10673
                          · linarith only [h10673, hlam, p10651_0]
                          · rcases p10651_3 (m.d 1 2) (by simp) with h10675 | h10675
                            · rcases p10651_3 (m.d 1 3) (by simp) with h10676 | h10676
                              · linarith only [h10227, h10676, hlam]
                              · linarith only [h10676, h6794, hlam]
                            · linarith only [h0, h10675, hlam]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10225, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h6794, hc01, hc14, hlam, hphi, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10227, h10549, h6794, hc01, hc34, hlam, hphi, ht12, ht23, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          rcases p10651_3 (m.d 0 1) (by simp) with h10684 | h10684
                          · linarith only [h10684, hlam, p10651_0]
                          · rcases p10651_3 (m.d 1 2) (by simp) with h10686 | h10686
                            · rcases p10651_3 (m.d 1 3) (by simp) with h10687 | h10687
                              · linarith only [h10549, h10687, hlam]
                              · linarith only [h10687, h6794, hlam]
                            · linarith only [h0, h10686, hlam]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10226, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h6794, hc01, hc15, hlam, hphi, p10651_1]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [h10598, hlam, p10651_0]
                        · have p10651_0 := h10651c.1
                          have p10651_1 := h10651c.2.1
                          have p10651_2 := h10651c.2.2.1
                          have p10651_3 := h10651c.2.2.2
                          linarith only [hlam, p10651_0]
                      · linarith only [h10223, h10227, h10650, h7647, hlam]
              · linarith only [h10223, h10598, h7647, hlam]
        · linarith only [h0, h10226, h8380, hlam]
      · linarith only [h0, h10225, h8379, hlam]
    · linarith only [h0, h10224, h8378, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h10700 | h10700
    · rcases m.htr 1 2 4 (by decide) (by decide) with h10701 | h10701
      · rcases m.htr 1 2 5 (by decide) (by decide) with h10702 | h10702
        · rcases m.htr 1 3 4 (by decide) (by decide) with h10703 | h10703
          · rcases m.htr 1 3 5 (by decide) (by decide) with h10704 | h10704
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10705 | h10705
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10706 | h10706
                · linarith only [h10706, h8378, h8381, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10708 | h10708
                  · linarith only [h10700, h10703, h10708, h8378, h8381, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10710 | h10710
                    · linarith only [h10223, h10710, h8379, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10712 | h10712
                      · linarith only [h10223, h10700, h10703, h10712, h6794, h8381, hc01, hc12, hlam, hphi]
                      · linarith only [h10700, h10703, h10705, h10712, h6794, h8381, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10715 | h10715
                · linarith only [h10715, h8378, h8381, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10717 | h10717
                  · linarith only [h10700, h10703, h10717, h8378, h8381, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10719 | h10719
                    · linarith only [h10703, h10705, h10719, h6794, h8381, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10721 | h10721
                      · linarith only [h10703, h10705, h10721, hlam]
                      · rcases h1bigk with h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c | h10723c
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h0, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h6794, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h7647, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h8170, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          rcases p10723_3 (m.d 0 1) (by simp) with h10729 | h10729
                          · linarith only [h10729, hlam, p10723_0]
                          · rcases p10723_3 (m.d 1 2) (by simp) with h10731 | h10731
                            · rcases p10723_3 (m.d 1 3) (by simp) with h10732 | h10732
                              · linarith only [h10700, h10732, hlam]
                              · linarith only [h10732, h6794, hlam]
                            · linarith only [h10731, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h6794, hc01, hc12, hlam, hphi, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h7647, hc01, hc12, hlam, hphi, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h8170, hc01, hc12, hlam, hphi, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          rcases p10723_3 (m.d 0 1) (by simp) with h10740 | h10740
                          · linarith only [h10740, hlam, p10723_0]
                          · rcases p10723_3 (m.d 1 2) (by simp) with h10742 | h10742
                            · rcases p10723_3 (m.d 1 3) (by simp) with h10743 | h10743
                              · rcases p10723_3 (m.d 1 4) (by simp) with h10744 | h10744
                                · linarith only [h10703, h10744, hlam]
                                · linarith only [h10744, h7647, hlam]
                              · linarith only [h10743, hlam, p10723_0]
                            · linarith only [h0, h10742, hlam]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10700, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10703, h6794, h8381, hc01, hc13, hlam, hphi, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10700, h10704, h10721, h6794, h8381, hc01, hc12, hlam, hphi, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10705, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10701, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10703, hlam, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10705, hlam, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          rcases p10723_3 (m.d 0 1) (by simp) with h10758 | h10758
                          · linarith only [h10758, hlam, p10723_0]
                          · rcases p10723_3 (m.d 1 2) (by simp) with h10760 | h10760
                            · rcases p10723_3 (m.d 1 3) (by simp) with h10761 | h10761
                              · rcases p10723_3 (m.d 1 4) (by simp) with h10762 | h10762
                                · linarith only [h10705, h10762, hlam]
                                · linarith only [h10762, h7647, hlam]
                              · linarith only [h10761, h6794, hlam]
                            · linarith only [h0, h10760, hlam]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10702, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h10704, hlam, p10723_0]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [h7647, hc01, hc15, hlam, hphi, p10723_1]
                        · have p10723_0 := h10723c.1
                          have p10723_1 := h10723c.2.1
                          have p10723_2 := h10723c.2.2.1
                          have p10723_3 := h10723c.2.2.2
                          linarith only [hlam, p10723_0]
            · linarith only [h10703, h10704, h6794, h8381, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h10772 | h10772
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10773 | h10773
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10774 | h10774
                · linarith only [h10703, h10774, h6794, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10776 | h10776
                  · linarith only [h10223, h10703, h10772, h10773, h10776, h8378, h8381, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h10703, h10772, h10776, hc23, hc34, hlam, hphi]
              · linarith only [h10703, h10772, h10773, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10780 | h10780
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10781 | h10781
                · linarith only [h0, h10781, h6794, h8378, h8381, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10783 | h10783
                  · linarith only [h10223, h10772, h10780, h10783, h6794, h8378, h8381, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10785 | h10785
                    · linarith only [h10223, h10785, h8379, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10787 | h10787
                      · rcases h1bigk with h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c | h10788c
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h0, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h6794, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h7647, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h8170, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          rcases p10788_3 (m.d 0 1) (by simp) with h10794 | h10794
                          · linarith only [h10794, hlam, p10788_0]
                          · rcases p10788_3 (m.d 1 2) (by simp) with h10796 | h10796
                            · rcases p10788_3 (m.d 1 3) (by simp) with h10797 | h10797
                              · linarith only [h10700, h10797, hlam]
                              · linarith only [h10797, h6794, hlam]
                            · linarith only [h10796, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h6794, hc01, hc12, hlam, hphi, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10223, h10780, h8381, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10223, h10780, h6794, h8381, hc01, hc12, hlam, hphi, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10772, hc01, hc35, hlam, hphi, ht12, ht23, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10700, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10703, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10772, hlam, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          rcases p10788_3 (m.d 0 1) (by simp) with h10810 | h10810
                          · linarith only [h10810, hlam, p10788_0]
                          · rcases p10788_3 (m.d 1 2) (by simp) with h10812 | h10812
                            · rcases p10788_3 (m.d 1 3) (by simp) with h10813 | h10813
                              · linarith only [h10703, h10813, hlam]
                              · linarith only [h10813, h6794, hlam]
                            · linarith only [h0, h10812, hlam]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10701, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h6794, hc01, hc14, hlam, hphi, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10703, h8170, hc01, hc34, hlam, hphi, ht12, ht23, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          rcases p10788_3 (m.d 0 1) (by simp) with h10821 | h10821
                          · linarith only [h10821, hlam, p10788_0]
                          · rcases p10788_3 (m.d 1 2) (by simp) with h10823 | h10823
                            · rcases p10788_3 (m.d 1 3) (by simp) with h10824 | h10824
                              · linarith only [h10772, h10824, hlam]
                              · linarith only [h10824, h6794, hlam]
                            · linarith only [h0, h10823, hlam]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10702, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h6794, hc01, hc15, hlam, hphi, p10788_1]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [h10780, hlam, p10788_0]
                        · have p10788_0 := h10788c.1
                          have p10788_1 := h10788c.2.1
                          have p10788_2 := h10788c.2.2.1
                          have p10788_3 := h10788c.2.2.2
                          linarith only [hlam, p10788_0]
                      · linarith only [h10703, h10780, h10787, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10833 | h10833
                · linarith only [h10833, h8378, h8381, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10835 | h10835
                  · linarith only [h10772, h10835, h6794, h8378, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10837 | h10837
                    · linarith only [h10703, h10780, h10837, h6794, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10839 | h10839
                      · linarith only [h10703, h10780, h10839, h6794, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h10703, h10839, h6794, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h10702, h8380, hlam]
      · linarith only [h0, h10701, h8379, hlam]
    · linarith only [h0, h10700, h8378, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 0 3 4 (by decide) (by decide) with h8381 | h8381
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380 h8381

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8380 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 0 3 4 (by decide) (by decide) with h10845 | h10845
  · rcases m.htr 0 4 5 (by decide) (by decide) with h10846 | h10846
    · linarith only [h10845, h10846, h8378, h8380, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10848 | h10848
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10849 | h10849
        · rcases m.htr 1 2 5 (by decide) (by decide) with h10850 | h10850
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10851 | h10851
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10852 | h10852
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10853 | h10853
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10854 | h10854
                  · linarith only [h10850, h10854, h8378, h8380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h10845, h10850, h10854, h8378, h8380, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10857 | h10857
                  · linarith only [h10850, h10857, h8378, h8380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h10845, h10850, h10857, h8378, h8380, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10860 | h10860
                · linarith only [h10846, h10851, h10852, h10860, h7647, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10862 | h10862
                  · linarith only [h10850, h10862, h8378, h8380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h10845, h10850, h10862, h8378, h8380, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h10845, h10850, h10851, h8378, h8380, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10866 | h10866
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10867 | h10867
              · linarith only [h10848, h10850, h10867, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10869 | h10869
                · linarith only [h10846, h10849, h10850, h10869, h7647, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10871 | h10871
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10872 | h10872
                    · linarith only [h0, h10850, h10867, h10872, h8378, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10874 | h10874
                      · linarith only [h0, h10850, h10872, h10874, h8379, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h0, h10850, h10871, h10874, h8378, hc34, hc45, hlam, hphi]
                  · linarith only [h10845, h10867, h10871, h6794, hc23, hc35, hlam, hphi]
            · linarith only [h10845, h10866, h6794, hlam]
        · linarith only [h0, h10849, h8379, hlam]
      · linarith only [h0, h10848, h8378, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h10881 | h10881
    · linarith only [h10881, h8379, h8380, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10883 | h10883
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10884 | h10884
        · rcases m.htr 1 2 5 (by decide) (by decide) with h10885 | h10885
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10886 | h10886
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10887 | h10887
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10888 | h10888
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10889 | h10889
                  · linarith only [h10845, h10889, h8378, h8380, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10891 | h10891
                    · linarith only [h10885, h10889, h10891, h8379, h8380, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10893 | h10893
                      · linarith only [h10881, h10883, h10887, h10891, h10893, h8379, h8380, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10895 | h10895
                        · linarith only [h10889, h10893, h10895, h8379, h8380, hc23, hc34, hlam, hphi]
                        · linarith only [h10845, h10883, h10886, h10888, h10895, h6794, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10898 | h10898
                  · linarith only [h10845, h10898, h6794, h8378, h8380, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10900 | h10900
                    · linarith only [h10885, h10898, h10900, h8379, h8380, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10902 | h10902
                      · linarith only [h10883, h10887, h10888, h10900, h10902, h8379, h8380, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10904 | h10904
                        · linarith only [h10886, h10888, h10904, hlam]
                        · rcases h1bigk with h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c | h10906c
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h0, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h6794, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h7647, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h8170, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            rcases p10906_3 (m.d 0 1) (by simp) with h10912 | h10912
                            · linarith only [h10912, hlam, p10906_0]
                            · rcases p10906_3 (m.d 1 2) (by simp) with h10914 | h10914
                              · rcases p10906_3 (m.d 1 3) (by simp) with h10915 | h10915
                                · linarith only [h10883, h10915, hlam]
                                · linarith only [h10915, h6794, hlam]
                              · linarith only [h10914, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10887, h10898, h10900, h8379, h8380, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10845, h10886, h6794, hc01, hc12, hlam, hphi, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h8170, hc01, hc12, hlam, hphi, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            rcases p10906_3 (m.d 0 1) (by simp) with h10923 | h10923
                            · linarith only [h10923, hlam, p10906_0]
                            · rcases p10906_3 (m.d 1 2) (by simp) with h10925 | h10925
                              · rcases p10906_3 (m.d 1 3) (by simp) with h10926 | h10926
                                · rcases p10906_3 (m.d 1 4) (by simp) with h10927 | h10927
                                  · linarith only [h10886, h10927, hlam]
                                  · linarith only [h10927, h7647, hlam]
                                · linarith only [h10926, hlam, p10906_0]
                              · linarith only [h0, h10925, hlam]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10883, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10845, h10886, h6794, hc01, hc13, hlam, hphi, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10883, h10887, h10898, h10900, h8379, h8380, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10888, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10884, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10886, hlam, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10888, hlam, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            rcases p10906_3 (m.d 0 1) (by simp) with h10941 | h10941
                            · linarith only [h10941, hlam, p10906_0]
                            · rcases p10906_3 (m.d 1 2) (by simp) with h10943 | h10943
                              · rcases p10906_3 (m.d 1 3) (by simp) with h10944 | h10944
                                · rcases p10906_3 (m.d 1 4) (by simp) with h10945 | h10945
                                  · linarith only [h10888, h10945, hlam]
                                  · linarith only [h10945, h7647, hlam]
                                · linarith only [h10944, h6794, hlam]
                              · linarith only [h0, h10943, hlam]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10885, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h10887, hlam, p10906_0]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [h7647, hc01, hc15, hlam, hphi, p10906_1]
                          · have p10906_0 := h10906c.1
                            have p10906_1 := h10906c.2.1
                            have p10906_2 := h10906c.2.2.1
                            have p10906_3 := h10906c.2.2.2
                            linarith only [hlam, p10906_0]
              · linarith only [h10845, h10886, h10887, h6794, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10955 | h10955
              · linarith only [h10885, h10886, h10955, h8378, h8380, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10957 | h10957
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10958 | h10958
                  · linarith only [h10885, h10886, h10958, h8378, h8380, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10960 | h10960
                    · linarith only [h10885, h10955, h10958, h10960, h8379, h8380, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10962 | h10962
                      · linarith only [h10845, h10881, h10885, h10962, h8379, h8380, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h10886, h10957, h10958, h10962, h8379, h8380, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10965 | h10965
                  · linarith only [h10885, h10965, h8378, h8380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10967 | h10967
                    · linarith only [h10885, h10955, h10965, h10967, h6794, h8379, h8380, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10969 | h10969
                      · linarith only [h10885, h10886, h10957, h10969, h6794, h8379, h8380, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10971 | h10971
                        · linarith only [h10886, h10957, h10971, h6794, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h10886, h10971, h6794, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10974 | h10974
            · linarith only [h10845, h10883, h10885, h10974, h6794, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10976 | h10976
              · linarith only [h10884, h10885, h10974, h10976, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10978 | h10978
                · linarith only [h10845, h10881, h10884, h10885, h10978, h6794, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10980 | h10980
                  · linarith only [h10974, h10980, h6794, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10982 | h10982
                    · linarith only [h10976, h10982, h6794, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10984 | h10984
                      · linarith only [h0, h10845, h10885, h10978, h10982, h10984, h7647, h8379, hc03, hc35, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10986 | h10986
                        · linarith only [h0, h10885, h10984, h10986, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h10974, h10986, h6794, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h10884, h8379, hlam]
      · linarith only [h0, h10883, h8378, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg8378 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8379 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  have h8378 := hg8378
  have h8379 := hg8379
  rcases m.htr 0 2 5 (by decide) (by decide) with h8380 | h8380
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 hg8378 hg8379 h8380

end R2N4
