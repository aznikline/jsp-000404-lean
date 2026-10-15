import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S5
import Jsp000404.R1LeavesN7_14S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9218000 in
set_option maxHeartbeats 9218000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3600 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h4239 | h4239
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4240 | h4240
    · linarith only [h0, h1, h4240, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4242 | h4242
      · linarith only [h0, h3600, h4242, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4244 | h4244
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4245 | h4245
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4246 | h4246
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4247 | h4247
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4248 | h4248
                · linarith only [h0, h3600, h4240, h4244, h4245, h4248, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4250 | h4250
                  · linarith only [h0, h3600, h4242, h4250, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4252 | h4252
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4253 | h4253
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4254 | h4254
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4255 | h4255
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4256 | h4256
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4257 | h4257
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4258 | h4258
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4259 | h4259
                                  · rcases h0bigk with h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c | h4260c
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h3600, h4248, h4253, hc02, hc23, hlam, hphi, p4260_1]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h1, hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h3600, hlam, p4260_1]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      rcases p4260_3 (m.d 0 1) (by simp) with h4265 | h4265
                                      · rcases p4260_3 (m.d 0 2) (by simp) with h4266 | h4266
                                        · linarith only [h0, h4266, hlam]
                                        · linarith only [h4244, h4266, hlam]
                                      · linarith only [h4239, h4265, hlam]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h0, hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4240, hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4242, hlam, p4260_1]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      rcases p4260_3 (m.d 0 1) (by simp) with h4274 | h4274
                                      · rcases p4260_3 (m.d 0 2) (by simp) with h4275 | h4275
                                        · rcases p4260_3 (m.d 0 3) (by simp) with h4276 | h4276
                                          · rcases p4260_3 (m.d 0 4) (by simp) with h4277 | h4277
                                            · rcases p4260_3 (m.d 0 5) (by simp) with h4278 | h4278
                                              · linarith only [h4244, h4278, hlam]
                                              · rcases h2bigk with h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c | h4280c
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h0, h3600, h4248, h4253, hc12, hc23, hlam, hphi, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4240, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4242, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  rcases p4280_3 (m.d 0 2) (by simp) with h4285 | h4285
                                                  · rcases p4280_3 (m.d 1 2) (by simp) with h4286 | h4286
                                                    · linarith only [h0, h4286, hlam]
                                                    · linarith only [h4252, h4286, hlam]
                                                  · linarith only [h4285, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h0, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4248, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4250, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h0, h3600, h4248, h4253, h4257, h4259, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4239, h4252, h4257, h4259, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4260_1, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  rcases p4280_3 (m.d 0 2) (by simp) with h4296 | h4296
                                                  · linarith only [h4240, h4296, hlam]
                                                  · linarith only [h0, h4296, hlam]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h3600, h4250, hc01, hc23, hlam, hphi, ht12, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h0, h3600, h4239, h4248, h4252, h4253, hlam, p4260_1, p4280_2]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4239, h4252, h4257, h4259, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4260_1, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  rcases p4280_3 (m.d 0 2) (by simp) with h4303 | h4303
                                                  · linarith only [h4242, h4303, hlam]
                                                  · linarith only [h0, h4303, hlam]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4256, hlam, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4239, h4242, h4252, hlam, p4260_1, p4280_2]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4244, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4252, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4257, hlam, p4280_1]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [h4258, hlam, p4280_0]
                                                · have p4280_0 := h4280c.1
                                                  have p4280_1 := h4280c.2.1
                                                  have p4280_2 := h4280c.2.2.1
                                                  have p4280_3 := h4280c.2.2.2
                                                  linarith only [hlam, p4280_0]
                                            · linarith only [h4247, h4277, hlam]
                                          · linarith only [h4246, h4276, hlam]
                                        · linarith only [h4244, h4275, hlam]
                                      · linarith only [h4239, h4274, hlam]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h0, h4252, h4257, h4259, hc45, hlam, hphi, ht0b, ht5b, p4260_1, u0elo2]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h0, h4252, h4257, h4259, hc45, hlam, hphi, ht0b, ht5b, p4260_1, u0elo2]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h0, h3600, h4252, h4257, h4259, hc45, hlam, hphi, ht0b, ht5b, p4260_1, u0elo2]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      rcases p4260_3 (m.d 0 1) (by simp) with h4322 | h4322
                                      · linarith only [h1, h4322, hlam]
                                      · linarith only [h4239, h4322, hlam]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h0, h4252, h4257, h4259, hc45, hlam, hphi, ht0b, ht5b, p4260_1, u0elo3]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h0, h4252, h4257, h4259, hc45, hlam, hphi, ht0b, ht5b, p4260_1, u0elo3]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4245, hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      rcases p4260_3 (m.d 0 1) (by simp) with h4329 | h4329
                                      · linarith only [h3600, h4329, hlam]
                                      · linarith only [h4239, h4329, hlam]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4239, hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4244, hlam, p4260_1]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4246, hlam, p4260_0]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [h4247, hlam, p4260_1]
                                    · have p4260_0 := h4260c.1
                                      have p4260_1 := h4260c.2.1
                                      have p4260_2 := h4260c.2.2.1
                                      have p4260_3 := h4260c.2.2.2
                                      linarith only [hlam, p4260_0]
                                  · linarith only [h0, h3600, h4248, h4252, h4253, h4258, h4259, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h3600, h4239, h4250, h4255, h4258, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                              · linarith only [h0, h3600, h4248, h4252, h4253, h4257, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h3600, h4248, h4252, h4253, h4256, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h3600, h4252, h4255, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h3600, h4252, h4253, h4254, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h4245, h4252, h4253, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h1, h4244, h4248, h4252, hc12, hc23, hlam, hphi]
              · linarith only [h0, h3600, h4244, h4247, hlam]
            · linarith only [h0, h1, h4244, h4246, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4347 | h4347
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4348 | h4348
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4349 | h4349
                · linarith only [h0, h4240, h4349, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4351 | h4351
                  · linarith only [h0, h4242, h4351, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4353 | h4353
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4354 | h4354
                      · linarith only [h0, h1, h4245, h4349, h4354, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h4353, h4354, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h3600, h4244, h4351, h4353, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h4244, h4245, h4348, hlam]
            · linarith only [h0, h1, h4244, h4347, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4360 | h4360
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4361 | h4361
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4362 | h4362
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4363 | h4363
                · linarith only [h0, h4240, h4363, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4365 | h4365
                  · linarith only [h0, h4242, h4365, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4367 | h4367
                    · linarith only [h0, h4244, h4367, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4369 | h4369
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4370 | h4370
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4371 | h4371
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4372 | h4372
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4373 | h4373
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4374 | h4374
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4375 | h4375
                                  · rcases h0bigk with h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c | h4376c
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h3600, h4363, h4369, hc02, hc23, hlam, hphi, p4376_1]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h1, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h3600, hlam, p4376_1]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h0, h3600, h4244, h4363, h4369, hc12, hc23, hlam, hphi, p4376_1]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h0, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4240, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4242, hlam, p4376_1]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4244, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4376_1, u0elo2]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      rcases p4376_3 (m.d 0 1) (by simp) with h4388 | h4388
                                      · linarith only [h1, h4388, hlam]
                                      · linarith only [h0, h4388, hlam]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h3600, h4239, h4367, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4376_1, u0elo2]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      rcases p4376_3 (m.d 0 1) (by simp) with h4393 | h4393
                                      · linarith only [h1, h4393, hlam]
                                      · linarith only [h4239, h4393, hlam]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4239, h4367, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4376_1, u0elo3]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      rcases p4376_3 (m.d 0 1) (by simp) with h4397 | h4397
                                      · linarith only [h3600, h4397, hlam]
                                      · linarith only [h0, h4397, hlam]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4360, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      rcases p4376_3 (m.d 0 1) (by simp) with h4402 | h4402
                                      · linarith only [h3600, h4402, hlam]
                                      · linarith only [h4239, h4402, hlam]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4239, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h0, h1, h4239, h4363, hc12, hc23, hlam, hphi, p4376_1]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4361, hlam, p4376_0]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [h4362, hlam, p4376_1]
                                    · have p4376_0 := h4376c.1
                                      have p4376_1 := h4376c.2.1
                                      have p4376_2 := h4376c.2.2.1
                                      have p4376_3 := h4376c.2.2.2
                                      linarith only [hlam, p4376_0]
                                  · rcases h0bigk with h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h0, h3600, h4363, h4369, hc12, hc23, hlam, hphi, p4410_1]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h1, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h3600, hlam, p4410_1]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h3600, h4239, h4363, h4369, h4371, h4375, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4410_1]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h0, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4240, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4242, hlam, p4410_1]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4244, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4410_1, u0elo2]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      rcases p4410_3 (m.d 0 1) (by simp) with h4422 | h4422
                                      · linarith only [h1, h4422, hlam]
                                      · linarith only [h0, h4422, hlam]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h3600, h4239, h4371, h4375, hc34, hlam, hphi, ht0b, ht45, ht5b, p4410_1, u0elo2]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4239, h4371, h4375, hc34, hlam, hphi, ht0b, ht45, ht5b, p4410_1, u0elo2]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4239, h4371, h4375, hc34, hlam, hphi, ht0b, ht45, ht5b, p4410_1, u0elo3]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      rcases p4410_3 (m.d 0 1) (by simp) with h4429 | h4429
                                      · linarith only [h3600, h4429, hlam]
                                      · linarith only [h0, h4429, hlam]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4360, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4239, h4360, h4371, h4375, hc34, hlam, hphi, ht0b, ht45, ht5b, p4410_1, u0elo2]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4239, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h0, h3600, h4239, h4363, h4369, hc12, hc23, hlam, hphi, p4410_1]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4361, hlam, p4410_0]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [h4362, hlam, p4410_1]
                                    · have p4410_0 := h4410c.1
                                      have p4410_1 := h4410c.2.1
                                      have p4410_2 := h4410c.2.2.1
                                      have p4410_3 := h4410c.2.2.2
                                      linarith only [hlam, p4410_0]
                                · linarith only [h3600, h4239, h4365, h4371, h4374, hlam]
                              · linarith only [h0, h3600, h4363, h4369, h4373, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h3600, h4363, h4369, h4372, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h3600, h4239, h4367, h4371, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h4239, h4367, h4370, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h4239, h4360, h4367, h4369, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h3600, h4239, h4362, hlam]
            · linarith only [h1, h4239, h4361, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4448 | h4448
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4449 | h4449
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4450 | h4450
                · linarith only [h0, h1, h4240, h4450, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4452 | h4452
                  · linarith only [h0, h1, h4242, h4360, h4452, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4454 | h4454
                    · linarith only [h0, h4244, h4454, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4456 | h4456
                      · linarith only [h1, h4239, h4360, h4450, h4454, h4456, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h4239, h4454, h4456, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h4239, h4360, h4449, hlam]
            · linarith only [h1, h4239, h4448, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4461 | h4461
    · linarith only [h0, h1, h4461, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4463 | h4463
      · linarith only [h0, h3600, h4463, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4465 | h4465
        · linarith only [h0, h4239, h4465, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4467 | h4467
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4468 | h4468
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4469 | h4469
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4470 | h4470
                · linarith only [h0, h4239, h4461, h4467, h4469, h4470, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4472 | h4472
                  · linarith only [h0, h4239, h4463, h4469, h4472, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4474 | h4474
                    · linarith only [h0, h4465, h4474, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4476 | h4476
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4477 | h4477
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4478 | h4478
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4479 | h4479
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4480 | h4480
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4481 | h4481
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4482 | h4482
                                  · rcases h0bigk with h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c | h4483c
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, h4239, h4470, h4476, h4478, hc12, hc23, hlam, hphi, p4483_1]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h1, hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h3600, hlam, p4483_1]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4239, hlam, p4483_1]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4461, hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4463, hlam, p4483_1]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4465, hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4483_1, u0elo2]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      rcases p4483_3 (m.d 0 1) (by simp) with h4495 | h4495
                                      · linarith only [h1, h4495, hlam]
                                      · linarith only [h0, h4495, hlam]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4467, h4482, hc45, hlam, hphi, ht0b, ht5b, p4483_1, u0elo2]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, h4239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4483_1, u0elo2]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4483_1, u0elo3]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      rcases p4483_3 (m.d 0 1) (by simp) with h4502 | h4502
                                      · linarith only [h3600, h4502, hlam]
                                      · linarith only [h0, h4502, hlam]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4467, hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, h4239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4483_1, u0elo3]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4483_1, u0elo4]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      rcases p4483_3 (m.d 0 1) (by simp) with h4509 | h4509
                                      · linarith only [h4239, h4509, hlam]
                                      · linarith only [h0, h4509, hlam]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4468, hlam, p4483_0]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [h4469, hlam, p4483_1]
                                    · have p4483_0 := h4483c.1
                                      have p4483_1 := h4483c.2.1
                                      have p4483_2 := h4483c.2.2.1
                                      have p4483_3 := h4483c.2.2.2
                                      linarith only [hlam, p4483_0]
                                  · rcases h0bigk with h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c | h4515c
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, h1, h4470, hc12, hc23, hlam, hphi, p4515_1]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h1, hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h3600, hlam, p4515_1]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4239, hlam, p4515_1]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4461, hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4463, hlam, p4515_1]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4465, hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4515_1, u0elo2]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      rcases p4515_3 (m.d 0 1) (by simp) with h4527 | h4527
                                      · linarith only [h1, h4527, hlam]
                                      · linarith only [h0, h4527, hlam]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4469, h4482, hc34, hlam, hphi, ht0b, ht45, ht5b, p4515_1, u0elo2]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, h4239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4515_1, u0elo2]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4515_1, u0elo3]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      rcases p4515_3 (m.d 0 1) (by simp) with h4534 | h4534
                                      · linarith only [h3600, h4534, hlam]
                                      · linarith only [h0, h4534, hlam]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4467, hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, h4239, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4515_1, u0elo3]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4515_1, u0elo4]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      rcases p4515_3 (m.d 0 1) (by simp) with h4541 | h4541
                                      · linarith only [h4239, h4541, hlam]
                                      · linarith only [h0, h4541, hlam]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4468, hlam, p4515_0]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [h4469, hlam, p4515_1]
                                    · have p4515_0 := h4515c.1
                                      have p4515_1 := h4515c.2.1
                                      have p4515_2 := h4515c.2.2.1
                                      have p4515_3 := h4515c.2.2.2
                                      linarith only [hlam, p4515_0]
                                · linarith only [h0, h3600, h4472, h4481, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h0, h1, h4470, h4480, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h4239, h4470, h4476, h4478, h4479, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h3600, h4467, h4469, h4478, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1, h4468, h4477, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1, h4467, h4476, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4553 | h4553
                · linarith only [h0, h3600, h4469, h4553, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4555 | h4555
                  · linarith only [h0, h3600, h4469, h4555, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4557 | h4557
                    · linarith only [h0, h4465, h4557, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4559 | h4559
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4560 | h4560
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4561 | h4561
                          · linarith only [h0, h3600, h4469, h4553, h4559, h4561, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h3600, h4561, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h4468, h4560, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h4467, h4559, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4566 | h4566
              · linarith only [h4467, h4468, h4566, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4568 | h4568
                · linarith only [h0, h1, h4468, h4568, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4570 | h4570
                  · linarith only [h0, h3600, h4463, h4570, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4572 | h4572
                    · linarith only [h0, h4465, h4572, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4574 | h4574
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4575 | h4575
                        · linarith only [h0, h3600, h4467, h4468, h4568, h4575, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h4575, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h4467, h4574, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4579 | h4579
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4580 | h4580
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4581 | h4581
                · linarith only [h0, h4461, h4581, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4583 | h4583
                  · linarith only [h0, h4463, h4583, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4585 | h4585
                    · linarith only [h0, h4465, h4585, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4587 | h4587
                      · linarith only [h0, h4239, h4467, h4579, h4581, h4587, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h4587, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h4467, h4579, h4580, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4591 | h4591
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4592 | h4592
                · linarith only [h0, h1, h4579, h4592, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4594 | h4594
                  · linarith only [h0, h1, h4463, h4579, h4594, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4596 | h4596
                    · linarith only [h0, h4465, h4596, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4598 | h4598
                      · linarith only [h0, h1, h4467, h4592, h4598, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h4598, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4601 | h4601
                · linarith only [h0, h1, h4579, h4601, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4603 | h4603
                  · linarith only [h0, h3600, h4591, h4603, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4605 | h4605
                    · linarith only [h0, h1, h4465, h4467, h4591, h4605, hc02, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4607 | h4607
                      · linarith only [h0, h1, h4467, h4601, h4607, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h4607, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 9218000 in
set_option maxHeartbeats 9218000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3600 | h3600
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h3600
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h3600

set_option maxHeartbeats 9218000 in
set_option maxHeartbeats 9218000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x0 m hb0 hb2 hb3 hb5 hg0 h1
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0_x1 m hb0 hb2 hb3 hb5 hg0 h1

end R2N4
