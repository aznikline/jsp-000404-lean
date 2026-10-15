import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3607 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3608 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3609 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h4228 | h4228
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4229 | h4229
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4230 | h4230
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4231 | h4231
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4232 | h4232
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4233 | h4233
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4234 | h4234
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4235 | h4235
                · linarith only [h3607, h3609, h4228, h4235, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4237 | h4237
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4238 | h4238
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4239 | h4239
                      · linarith only [h3609, h4228, h4232, h4239, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h3607, h3609, h4237, h4238, h4239, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h3609, h4228, h4229, h4230, h4232, h4238, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h3609, h4228, h4230, h4232, h4237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h3609, h4228, h4229, h4230, h4232, h4234, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h3609, h4228, h4232, h4233, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4246 | h4246
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4247 | h4247
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4248 | h4248
                · linarith only [h2760, h4232, h4248, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4250 | h4250
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4251 | h4251
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4252 | h4252
                      · rcases h3bigk with h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c | h4253c
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h2760, hlam, p4253_1]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4250, h4252, hc03, hlam, hphi, ht0b, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h3609, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h2760, h4232, h4252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4232, hc03, hc34, hlam, hphi, p4253_1]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4232, h4250, h4252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4232, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4232, h4252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h3607, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4230, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4248, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h2760, h3607, h4232, h4252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4228, h4252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p4253_1]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4250, h4252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4253_1, u4ehi4]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          rcases p4253_3 (m.d 0 3) (by simp) with h4273 | h4273
                          · linarith only [h3609, h4273, hlam]
                          · linarith only [h4228, h4273, hlam]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4228, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4246, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4250, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [h4252, hlam, p4253_0]
                        · have p4253_0 := h4253c.1
                          have p4253_1 := h4253c.2.1
                          have p4253_2 := h4253c.2.2.1
                          have p4253_3 := h4253c.2.2.2
                          linarith only [hlam, p4253_0]
                      · linarith only [h3607, h3609, h4229, h4250, h4252, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4248, h4250, h4251, hlam]
                  · linarith only [h3609, h4228, h4250, hc23, hc34, hlam, hphi]
              · linarith only [h2760, h3404, h4228, h4229, h4232, h4247, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h2760, h4228, h4246, hlam]
        · linarith only [h0, h3608, h4231, hlam]
      · linarith only [h0, h3607, h4230, hlam]
    · linarith only [h3609, h4228, h4229, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4289 | h4289
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4290 | h4290
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4291 | h4291
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4292 | h4292
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4293 | h4293
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4294 | h4294
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4295 | h4295
                · linarith only [h0, h2760, h3607, h3609, h4295, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4297 | h4297
                  · linarith only [h3607, h4228, h4297, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4299 | h4299
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4300 | h4300
                      · rcases h3bigk with h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c | h4301c
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h2760, hlam, p4301_1]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4228, hc23, hc35, hlam, hphi, p4301_1]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h3609, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4228, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          rcases p4301_3 (m.d 0 3) (by simp) with h4307 | h4307
                          · linarith only [h2760, h4307, hlam]
                          · rcases p4301_3 (m.d 1 3) (by simp) with h4309 | h4309
                            · rcases p4301_3 (m.d 2 3) (by simp) with h4310 | h4310
                              · linarith only [h4290, h4310, hlam]
                              · rcases p4301_3 (m.d 3 4) (by simp) with h4312 | h4312
                                · linarith only [h4292, h4312, hlam]
                                · linarith only [h3609, h4312, hlam]
                            · linarith only [h2760, h4309, hlam]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          rcases p4301_3 (m.d 0 3) (by simp) with h4317 | h4317
                          · linarith only [h2760, h4317, hlam]
                          · linarith only [h3607, h4317, hlam]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h3608, h3609, h4299, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4301_1, u4ehi4]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h2760, h4228, h4290, hc01, hc12, hlam, hphi, p4301_1]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h3607, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4290, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4295, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4297, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h2760, h4290, h4292, hc01, hc12, hlam, hphi, p4301_1]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4292, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          rcases p4301_3 (m.d 0 3) (by simp) with h4329 | h4329
                          · linarith only [h3609, h4329, hlam]
                          · linarith only [h3607, h4329, hlam]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h2760, h4228, h4292, hc01, hc14, hlam, hphi, p4301_1]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h2760, h4290, h4293, hc01, hc12, hlam, hphi, p4301_1]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4293, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          rcases p4301_3 (m.d 0 3) (by simp) with h4336 | h4336
                          · linarith only [h4228, h4336, hlam]
                          · linarith only [h3607, h4336, hlam]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [h4300, hlam, p4301_0]
                        · have p4301_0 := h4301c.1
                          have p4301_1 := h4301c.2.1
                          have p4301_2 := h4301c.2.2.1
                          have p4301_3 := h4301c.2.2.2
                          linarith only [hlam, p4301_0]
                      · linarith only [h0, h3608, h4299, h4300, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h3609, h4289, h4290, h4292, h4299, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h3609, h4289, h4290, h4292, h4294, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h3609, h4289, h4292, h4293, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4345 | h4345
            · linarith only [h2760, h4228, h4292, h4345, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4347 | h4347
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4348 | h4348
                · linarith only [h2760, h4292, h4348, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4350 | h4350
                  · linarith only [h2760, h4345, h4350, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4352 | h4352
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4353 | h4353
                      · rcases h3bigk with h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h2760, hlam, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h2760, h4345, h4353, hc23, hc34, hlam, hphi, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h3609, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4228, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4345, h4353, hc03, hc34, hlam, hphi, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4345, h4353, hc23, hc34, hlam, hphi, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4292, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4345, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h3607, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4290, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4348, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4350, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          rcases p4354_3 (m.d 0 3) (by simp) with h4370 | h4370
                          · linarith only [h4370, hlam, p4354_0]
                          · rcases p4354_3 (m.d 1 3) (by simp) with h4372 | h4372
                            · linarith only [h4292, h4372, hlam]
                            · linarith only [h2760, h4372, hlam]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          rcases p4354_3 (m.d 0 3) (by simp) with h4376 | h4376
                          · linarith only [h3609, h4376, hlam]
                          · linarith only [h3607, h4376, hlam]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h2760, h4228, hc01, hc34, hlam, hphi, ht12, ht23, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          rcases p4354_3 (m.d 0 3) (by simp) with h4381 | h4381
                          · linarith only [h4381, hlam, p4354_0]
                          · rcases p4354_3 (m.d 1 3) (by simp) with h4383 | h4383
                            · linarith only [h4345, h4383, hlam]
                            · linarith only [h2760, h4383, hlam]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h2760, hc01, hc35, hlam, hphi, ht12, ht23, p4354_1]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          rcases p4354_3 (m.d 0 3) (by simp) with h4387 | h4387
                          · linarith only [h4228, h4387, hlam]
                          · linarith only [h3607, h4387, hlam]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [h4353, hlam, p4354_0]
                        · have p4354_0 := h4354c.1
                          have p4354_1 := h4354c.2.1
                          have p4354_2 := h4354c.2.2.1
                          have p4354_3 := h4354c.2.2.2
                          linarith only [hlam, p4354_0]
                      · linarith only [h0, h3608, h4352, h4353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4393 | h4393
                      · rcases h3bigk with h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c | h4394c
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h2760, hlam, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h3609, hc23, hc34, hlam, hphi, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h3609, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4228, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4292, hc03, hc34, hlam, hphi, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4292, hc23, hc34, hlam, hphi, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4292, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4345, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h3607, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4290, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4348, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4350, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          rcases p4394_3 (m.d 0 3) (by simp) with h4410 | h4410
                          · linarith only [h4410, hlam, p4394_0]
                          · rcases p4394_3 (m.d 1 3) (by simp) with h4412 | h4412
                            · linarith only [h4292, h4412, hlam]
                            · linarith only [h2760, h4412, hlam]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          rcases p4394_3 (m.d 0 3) (by simp) with h4416 | h4416
                          · linarith only [h3609, h4416, hlam]
                          · linarith only [h3607, h4416, hlam]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h2760, h4228, hc01, hc34, hlam, hphi, ht12, ht23, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          rcases p4394_3 (m.d 0 3) (by simp) with h4421 | h4421
                          · linarith only [h4421, hlam, p4394_0]
                          · rcases p4394_3 (m.d 1 3) (by simp) with h4423 | h4423
                            · linarith only [h4345, h4423, hlam]
                            · linarith only [h2760, h4423, hlam]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h2760, hc01, hc35, hlam, hphi, ht12, ht23, p4394_1]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          rcases p4394_3 (m.d 0 3) (by simp) with h4427 | h4427
                          · linarith only [h4228, h4427, hlam]
                          · linarith only [h3607, h4427, hlam]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [h4393, hlam, p4394_0]
                        · have p4394_0 := h4394c.1
                          have p4394_1 := h4394c.2.1
                          have p4394_2 := h4394c.2.2.1
                          have p4394_3 := h4394c.2.2.2
                          linarith only [hlam, p4394_0]
                      · linarith only [h3404, h4289, h4292, h4393, hlam]
              · linarith only [h3404, h4289, h4347, hlam]
        · linarith only [h0, h3608, h4291, hlam]
      · linarith only [h0, h3607, h4290, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4436 | h4436
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4437 | h4437
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4438 | h4438
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4439 | h4439
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4440 | h4440
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4441 | h4441
                · linarith only [h3607, h3609, h4441, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4443 | h4443
                  · linarith only [h3607, h4228, h4443, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4445 | h4445
                    · linarith only [h3608, h4289, h4445, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4447 | h4447
                      · linarith only [h3608, h4289, h4436, h4438, h4447, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h2760, h3609, h4440, h4447, hc01, hc14, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4450 | h4450
                · linarith only [h3607, h3609, h4450, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4452 | h4452
                  · linarith only [h3607, h4228, h4452, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4454 | h4454
                    · linarith only [h3404, h4440, h4454, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4456 | h4456
                      · linarith only [h4438, h4440, h4456, hlam]
                      · rcases h3bigk with h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c | h4458c
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h2760, hlam, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h3609, hc23, hc34, hlam, hphi, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h3609, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4228, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          rcases p4458_3 (m.d 0 3) (by simp) with h4464 | h4464
                          · linarith only [h2760, h4464, hlam]
                          · rcases p4458_3 (m.d 1 3) (by simp) with h4466 | h4466
                            · rcases p4458_3 (m.d 2 3) (by simp) with h4467 | h4467
                              · linarith only [h4436, h4467, hlam]
                              · rcases p4458_3 (m.d 3 4) (by simp) with h4469 | h4469
                                · linarith only [h4438, h4469, hlam]
                                · linarith only [h3609, h4469, hlam]
                            · linarith only [h2760, h4466, hlam]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          rcases p4458_3 (m.d 0 3) (by simp) with h4474 | h4474
                          · linarith only [h2760, h4474, hlam]
                          · linarith only [h3607, h4474, hlam]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h2760, h3609, h4436, hc01, hc12, hlam, hphi, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h2760, h4228, h4436, hc01, hc12, hlam, hphi, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h3607, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4436, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4450, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4452, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h2760, h4436, h4438, hc01, hc12, hlam, hphi, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4438, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4438, h4440, hc23, hc45, hlam, hphi, ht34, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4456, hlam, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h2760, h4436, h4439, hc01, hc12, hlam, hphi, p4458_1]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h4439, hlam, p4458_0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          rcases p4458_3 (m.d 0 3) (by simp) with h4491 | h4491
                          · linarith only [h4228, h4491, hlam]
                          · linarith only [h3607, h4491, hlam]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [h3609, h4436, h4439, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4458_1, u4ehi0]
                        · have p4458_0 := h4458c.1
                          have p4458_1 := h4458c.2.1
                          have p4458_2 := h4458c.2.2.1
                          have p4458_3 := h4458c.2.2.2
                          linarith only [hlam, p4458_0]
            · linarith only [h2760, h3609, h4438, h4439, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4497 | h4497
            · linarith only [h2760, h4228, h4438, h4497, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4499 | h4499
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4500 | h4500
                · linarith only [h2760, h4438, h4500, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4502 | h4502
                  · linarith only [h2760, h3607, h3609, h4289, h4438, h4497, h4499, h4502, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4504 | h4504
                    · linarith only [h3608, h4289, h4504, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4506 | h4506
                      · rcases h3bigk with h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h2760, hlam, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h3609, h4289, h4438, h4499, hc23, hc34, hlam, hphi, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h3609, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4228, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4497, hc03, hc35, hlam, hphi, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4497, hc23, hc35, hlam, hphi, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4438, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4497, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h3607, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4436, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4500, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4502, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          rcases p4507_3 (m.d 0 3) (by simp) with h4523 | h4523
                          · linarith only [h4523, hlam, p4507_0]
                          · rcases p4507_3 (m.d 1 3) (by simp) with h4525 | h4525
                            · linarith only [h4438, h4525, hlam]
                            · linarith only [h2760, h4525, hlam]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          rcases p4507_3 (m.d 0 3) (by simp) with h4529 | h4529
                          · linarith only [h3609, h4529, hlam]
                          · linarith only [h3607, h4529, hlam]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h2760, h4228, hc01, hc34, hlam, hphi, ht12, ht23, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          rcases p4507_3 (m.d 0 3) (by simp) with h4534 | h4534
                          · linarith only [h4534, hlam, p4507_0]
                          · rcases p4507_3 (m.d 1 3) (by simp) with h4536 | h4536
                            · linarith only [h4497, h4536, hlam]
                            · linarith only [h2760, h4536, hlam]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h2760, hc01, hc35, hlam, hphi, ht12, ht23, p4507_1]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          rcases p4507_3 (m.d 0 3) (by simp) with h4540 | h4540
                          · linarith only [h4228, h4540, hlam]
                          · linarith only [h3607, h4540, hlam]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [h4506, hlam, p4507_0]
                        · have p4507_0 := h4507c.1
                          have p4507_1 := h4507c.2.1
                          have p4507_2 := h4507c.2.2.1
                          have p4507_3 := h4507c.2.2.2
                          linarith only [hlam, p4507_0]
                      · linarith only [h4438, h4499, h4506, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4546 | h4546
                · linarith only [h2760, h4438, h4546, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4548 | h4548
                  · linarith only [h3607, h4228, h4548, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4550 | h4550
                    · linarith only [h3404, h4499, h4550, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4552 | h4552
                      · linarith only [h2760, h4438, h4499, h4552, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2760, h4438, h4552, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h3608, h4437, hlam]
      · linarith only [h0, h3607, h4436, hlam]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3607 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3608 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h3609 | h3609
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x0_x0 m hb3 hb4 hg0 h2760 h3404 h3607 h3608 h3609
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x0_x1 m hb3 hb4 hg0 h2760 h3404 h3607 h3608 h3609

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3607 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3608 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h4557 | h4557
  · linarith only [h3607, h3608, h4557, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4559 | h4559
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4560 | h4560
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4561 | h4561
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4562 | h4562
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4563 | h4563
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4564 | h4564
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4565 | h4565
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4566 | h4566
                  · linarith only [h2760, h3607, h3608, h4557, h4562, h4566, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4568 | h4568
                    · linarith only [h3607, h3608, h4561, h4563, h4566, h4568, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h3607, h3608, h4559, h4561, h4563, h4566, h4568, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h3404, h4560, h4565, hlam]
              · linarith only [h4557, h4559, h4560, h4563, h4564, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4573 | h4573
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4574 | h4574
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4575 | h4575
                  · linarith only [h3607, h3608, h4562, h4563, h4575, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4577 | h4577
                    · linarith only [h3607, h3608, h4562, h4577, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h3607, h3608, h4559, h4562, h4577, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h3607, h3608, h4559, h4560, h4562, h4574, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h2760, h3607, h3608, h4559, h4562, h4573, hc01, hc12, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4582 | h4582
            · linarith only [h4557, h4559, h4561, h4562, h4582, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4584 | h4584
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4585 | h4585
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4586 | h4586
                  · linarith only [h2760, h3607, h4582, h4586, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4588 | h4588
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4589 | h4589
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4590 | h4590
                        · linarith only [h0, h3607, h4562, h4588, h4590, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h2760, h4561, h4562, h4585, h4586, h4590, hc01, hc15, hlam, hphi]
                      · linarith only [h0, h3607, h4559, h4560, h4562, h4589, hlam]
                    · linarith only [h0, h3607, h4559, h4562, h4586, h4588, hc23, hc34, hlam, hphi]
                · linarith only [h0, h3404, h3607, h4559, h4560, h4562, h4585, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2760, h3607, h4559, h4562, h4584, hc01, hc24, hlam, hphi, ht12]
        · linarith only [h0, h3607, h4561, hlam]
      · linarith only [h3607, h3608, h4559, h4560, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4599 | h4599
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4600 | h4600
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4601 | h4601
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4602 | h4602
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4603 | h4603
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4604 | h4604
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4605 | h4605
                  · linarith only [h0, h2760, h3607, h4557, h4605, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4607 | h4607
                    · linarith only [h2760, h3607, h3608, h4559, h4600, h4602, h4605, h4607, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4609 | h4609
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4610 | h4610
                        · rcases h3bigk with h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c | h4611c
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h2760, hlam, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4559, hc23, hc35, hlam, hphi, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4557, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4559, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            rcases p4611_3 (m.d 0 3) (by simp) with h4617 | h4617
                            · linarith only [h2760, h4617, hlam]
                            · rcases p4611_3 (m.d 1 3) (by simp) with h4619 | h4619
                              · rcases p4611_3 (m.d 2 3) (by simp) with h4620 | h4620
                                · linarith only [h4600, h4620, hlam]
                                · rcases p4611_3 (m.d 3 4) (by simp) with h4622 | h4622
                                  · linarith only [h4602, h4622, hlam]
                                  · linarith only [h4557, h4622, hlam]
                              · linarith only [h2760, h4619, hlam]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h3607, h3608, h4602, h4605, hlam, p4611_2]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h3607, h3608, h4600, h4605, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h2760, h4559, h4600, hc01, hc12, hlam, hphi, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h3607, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4600, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4605, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4607, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h2760, h4600, h4602, hc01, hc12, hlam, hphi, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4602, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            rcases p4611_3 (m.d 0 3) (by simp) with h4637 | h4637
                            · linarith only [h4557, h4637, hlam]
                            · linarith only [h3607, h4637, hlam]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h2760, h4559, h4600, h4602, hc01, hc12, hlam, hphi, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h2760, h4600, h4603, hc01, hc12, hlam, hphi, p4611_1]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4603, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            rcases p4611_3 (m.d 0 3) (by simp) with h4644 | h4644
                            · linarith only [h4559, h4644, hlam]
                            · linarith only [h3607, h4644, hlam]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [h4610, hlam, p4611_0]
                          · have p4611_0 := h4611c.1
                            have p4611_1 := h4611c.2.1
                            have p4611_2 := h4611c.2.2.1
                            have p4611_3 := h4611c.2.2.2
                            linarith only [hlam, p4611_0]
                        · linarith only [h2760, h3608, h4557, h4599, h4610, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h3608, h4599, h4609, hlam]
                · linarith only [h3404, h3608, h4599, h4604, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h4557, h4599, h4602, h4603, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4653 | h4653
              · linarith only [h2760, h4559, h4602, h4653, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4655 | h4655
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4656 | h4656
                  · linarith only [h3607, h3608, h4601, h4602, h4656, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4658 | h4658
                    · linarith only [h2760, h3607, h3608, h4601, h4653, h4658, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4660 | h4660
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4661 | h4661
                        · rcases h3bigk with h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c | h4662c
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h2760, hlam, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h2760, h4653, hc23, hc35, hlam, hphi, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4557, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4559, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4653, hc03, hc35, hlam, hphi, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4653, hc23, hc35, hlam, hphi, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4602, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4653, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h3607, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4600, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4656, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4658, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            rcases p4662_3 (m.d 0 3) (by simp) with h4678 | h4678
                            · linarith only [h4678, hlam, p4662_0]
                            · rcases p4662_3 (m.d 1 3) (by simp) with h4680 | h4680
                              · linarith only [h4602, h4680, hlam]
                              · linarith only [h2760, h4680, hlam]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            rcases p4662_3 (m.d 0 3) (by simp) with h4684 | h4684
                            · linarith only [h4557, h4684, hlam]
                            · linarith only [h3607, h4684, hlam]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h2760, h4559, hc01, hc34, hlam, hphi, ht12, ht23, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            rcases p4662_3 (m.d 0 3) (by simp) with h4689 | h4689
                            · linarith only [h4689, hlam, p4662_0]
                            · rcases p4662_3 (m.d 1 3) (by simp) with h4691 | h4691
                              · linarith only [h4653, h4691, hlam]
                              · linarith only [h2760, h4691, hlam]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h2760, hc01, hc35, hlam, hphi, ht12, ht23, p4662_1]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            rcases p4662_3 (m.d 0 3) (by simp) with h4695 | h4695
                            · linarith only [h4559, h4695, hlam]
                            · linarith only [h3607, h4695, hlam]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [h4661, hlam, p4662_0]
                          · have p4662_0 := h4662c.1
                            have p4662_1 := h4662c.2.1
                            have p4662_2 := h4662c.2.2.1
                            have p4662_3 := h4662c.2.2.2
                            linarith only [hlam, p4662_0]
                        · linarith only [h3608, h4599, h4601, h4661, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h3608, h4599, h4660, hlam]
                · linarith only [h3608, h4599, h4601, h4655, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4703 | h4703
            · linarith only [h4557, h4599, h4600, h4601, h4703, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4705 | h4705
              · linarith only [h2760, h4559, h4600, h4601, h4705, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4707 | h4707
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4708 | h4708
                  · linarith only [h2760, h4703, h4708, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4710 | h4710
                    · linarith only [h2760, h3607, h4705, h4710, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4712 | h4712
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4713 | h4713
                        · rcases h3bigk with h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c | h4714c
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h2760, hlam, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h2760, h4705, hc23, hc35, hlam, hphi, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4557, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4559, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4705, hc03, hc35, hlam, hphi, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4600, h4601, h4708, hc23, hc34, hlam, hphi, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4703, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4705, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h3607, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4600, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4708, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4710, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            rcases p4714_3 (m.d 0 3) (by simp) with h4730 | h4730
                            · linarith only [h4730, hlam, p4714_0]
                            · rcases p4714_3 (m.d 1 3) (by simp) with h4732 | h4732
                              · linarith only [h4703, h4732, hlam]
                              · linarith only [h2760, h4732, hlam]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            rcases p4714_3 (m.d 0 3) (by simp) with h4736 | h4736
                            · linarith only [h4557, h4736, hlam]
                            · linarith only [h3607, h4736, hlam]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h2760, h4559, hc01, hc34, hlam, hphi, ht12, ht23, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            rcases p4714_3 (m.d 0 3) (by simp) with h4741 | h4741
                            · linarith only [h4741, hlam, p4714_0]
                            · rcases p4714_3 (m.d 1 3) (by simp) with h4743 | h4743
                              · linarith only [h4705, h4743, hlam]
                              · linarith only [h2760, h4743, hlam]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h2760, hc01, hc35, hlam, hphi, ht12, ht23, p4714_1]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            rcases p4714_3 (m.d 0 3) (by simp) with h4747 | h4747
                            · linarith only [h4559, h4747, hlam]
                            · linarith only [h3607, h4747, hlam]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [h4713, hlam, p4714_0]
                          · have p4714_0 := h4714c.1
                            have p4714_1 := h4714c.2.1
                            have p4714_2 := h4714c.2.2.1
                            have p4714_3 := h4714c.2.2.2
                            linarith only [hlam, p4714_0]
                        · linarith only [h0, h3404, h4599, h4601, h4708, h4713, hc01, hc14, hlam, hphi]
                      · linarith only [h3404, h4599, h4601, h4712, hlam]
                · linarith only [h3404, h4599, h4707, hlam]
        · linarith only [h0, h3607, h4600, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4756 | h4756
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4757 | h4757
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4758 | h4758
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4759 | h4759
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4760 | h4760
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4761 | h4761
                  · linarith only [h2760, h3607, h3608, h4557, h4599, h4756, h4758, h4760, h4761, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4763 | h4763
                    · linarith only [h3607, h3608, h4599, h4756, h4758, h4760, h4763, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4765 | h4765
                      · linarith only [h3607, h3608, h4599, h4756, h4758, h4761, h4765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3607, h3608, h4765, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h3607, h3608, h4757, h4760, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2760, h4557, h4758, h4759, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4770 | h4770
              · linarith only [h2760, h4559, h4758, h4770, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4772 | h4772
                · linarith only [h3607, h3608, h4599, h4758, h4772, hc23, hc34, hlam, hphi]
                · linarith only [h3607, h3608, h4757, h4772, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4775 | h4775
            · linarith only [h2760, h4557, h4756, h4757, h4775, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4777 | h4777
              · linarith only [h2760, h4559, h4756, h4757, h4777, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4779 | h4779
                · linarith only [h3607, h3608, h4599, h4775, h4779, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4781 | h4781
                  · linarith only [h0, h3607, h4757, h4781, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4783 | h4783
                    · linarith only [h3607, h4559, h4783, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4785 | h4785
                      · linarith only [h3404, h3607, h3608, h4779, h4781, h4785, hc23, hc34, hlam, hphi]
                      · linarith only [h3607, h3608, h4785, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h3607, h3608, h4756, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3607 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3608 | h3608
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x0 m hb3 hb4 hg0 h2760 h3404 h3607 h3608
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1_x0_x1 m hb3 hb4 hg0 h2760 h3404 h3607 h3608

end R2N4
