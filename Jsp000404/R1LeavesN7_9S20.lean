import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S17
import Jsp000404.R1LeavesN7_9S18
import Jsp000404.R1LeavesN7_9S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1_x1_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h13831 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14484 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14485 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 4 5 (by decide) (by decide) with h15212 | h15212
  · linarith only [h14484, h14485, h15212, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h15214 | h15214
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15215 | h15215
      · rcases m.htr 1 3 4 (by decide) (by decide) with h15216 | h15216
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15217 | h15217
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15218 | h15218
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15219 | h15219
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15220 | h15220
                · linarith only [h14484, h14485, h15214, h15220, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h11548, h15217, h15220, hc01, hc13, hlam, hphi]
              · linarith only [h0, h11548, h14484, h15214, h15219, h7360, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15224 | h15224
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15225 | h15225
                · linarith only [h14484, h14485, h15214, h15225, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h11548, h15214, h15217, h15225, hc01, hc12, hlam, hphi]
              · linarith only [h0, h11548, h14484, h15214, h15224, h7360, hc01, hc12, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15229 | h15229
            · linarith only [h15212, h15216, h15217, h15229, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15231 | h15231
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15232 | h15232
                · linarith only [h15214, h15217, h15232, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15234 | h15234
                  · linarith only [h15215, h15229, h15234, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15236 | h15236
                    · linarith only [h0, h11548, h13831, h14484, h15214, h15215, h15217, h15229, h15236, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases h3bigk with h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c | h15238c
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h7360, hlam, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h11548, hlam, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h11548, h15214, h15217, h15236, hc34, hc45, hlam, hphi, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h14485, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15217, h15236, hc03, hc45, hlam, hphi, ht34, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15217, h15236, hc23, hc45, hlam, hphi, ht34, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15217, h15236, hc34, hc45, hlam, hphi, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15217, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15214, h7360, hc01, hc12, hlam, hphi, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15214, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15214, h15217, h15236, hc34, hc45, hlam, hphi, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15232, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h14484, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15216, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15231, hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [hlam, p15238_0]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15236, hlam, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h14484, h15236, hc34, hc45, hlam, hphi, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h15236, h7360, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [h0, h13831, h15231, h15236, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15238_1]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        rcases p15238_3 (m.d 0 3) (by simp) with h15262 | h15262
                        · linarith only [h14485, h15262, hlam]
                        · linarith only [h14484, h15262, hlam]
                      · have p15238_0 := h15238c.1
                        have p15238_1 := h15238c.2.1
                        have p15238_2 := h15238c.2.2.1
                        have p15238_3 := h15238c.2.2.2
                        linarith only [hlam, p15238_0]
              · linarith only [h0, h11548, h14484, h15231, h7360, hc01, hc13, hlam, hphi]
        · linarith only [h14484, h15216, h7360, hlam]
      · linarith only [h0, h11548, h15214, h15215, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15269 | h15269
      · linarith only [h0, h13831, h15214, h15269, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h15271 | h15271
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15272 | h15272
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15273 | h15273
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15274 | h15274
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15275 | h15275
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15276 | h15276
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15277 | h15277
                    · linarith only [h14484, h14485, h15212, h15272, h15277, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases h3bigk with h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c | h15279c
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h7360, hlam, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h11548, hlam, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14485, h15214, h15271, h15273, h15277, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14485, hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        rcases p15279_3 (m.d 0 3) (by simp) with h15285 | h15285
                        · linarith only [h15285, h7360, hlam]
                        · rcases p15279_3 (m.d 1 3) (by simp) with h15287 | h15287
                          · rcases p15279_3 (m.d 2 3) (by simp) with h15288 | h15288
                            · rcases p15279_3 (m.d 3 4) (by simp) with h15289 | h15289
                              · linarith only [h15271, h15289, hlam]
                              · rcases p15279_3 (m.d 3 5) (by simp) with h15291 | h15291
                                · linarith only [h15272, h15291, hlam]
                                · linarith only [h14485, h15291, hlam]
                            · linarith only [h11548, h15288, hlam]
                          · linarith only [h15287, h7360, hlam]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h15214, hlam, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14484, h14485, h15271, h15273, h15277, hlam, p15279_2]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14484, h14485, h15214, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        rcases p15279_3 (m.d 0 3) (by simp) with h15300 | h15300
                        · linarith only [h11548, h15300, hlam]
                        · rcases p15279_3 (m.d 1 3) (by simp) with h15302 | h15302
                          · linarith only [h15214, h15302, hlam]
                          · linarith only [h15302, h7360, hlam]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14484, h14485, h15214, h15272, hlam, p15279_2]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14484, h14485, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14484, hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h15271, hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h15274, hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h15277, hlam, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h14484, h15272, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15279_1]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h15272, hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [h15275, hlam, p15279_0]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        rcases p15279_3 (m.d 0 3) (by simp) with h15317 | h15317
                        · linarith only [h14485, h15317, hlam]
                        · linarith only [h14484, h15317, hlam]
                      · have p15279_0 := h15279c.1
                        have p15279_1 := h15279c.2.1
                        have p15279_2 := h15279c.2.2.1
                        have p15279_3 := h15279c.2.2.2
                        linarith only [hlam, p15279_0]
                  · linarith only [h0, h15269, h15273, h15276, hc01, hc14, hlam, hphi]
                · linarith only [h0, h13831, h15212, h15214, h15271, h15273, h15275, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h14484, h14485, h15214, h15272, h15274, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15324 | h15324
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15325 | h15325
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15326 | h15326
                  · linarith only [h0, h15269, h15273, h15326, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h15269, h15326, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h11548, h15272, h15325, hc01, hc13, hlam, hphi]
              · linarith only [h14484, h15214, h15324, h7360, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15331 | h15331
            · linarith only [h15212, h15271, h15272, h15331, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15333 | h15333
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15334 | h15334
                · linarith only [h15272, h15334, h7360, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15214, h15334, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h14484, h15214, h15333, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
        · linarith only [h14484, h15271, h7360, hlam]

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h13831 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14484 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 5 (by decide) (by decide) with h14485 | h14485
  · exact r1l7_13_24_L_I_H_I_s11_x1_x1_x0_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h13831 h14484 h14485
  · exact r1l7_13_24_L_I_H_I_s11_x1_x1_x0_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h13831 h14484 h14485

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h13831 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14484 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 5 (by decide) (by decide) with h15339 | h15339
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15340 | h15340
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15341 | h15341
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15342 | h15342
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15343 | h15343
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15344 | h15344
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15345 | h15345
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15346 | h15346
                · linarith only [h14484, h15339, h15341, h15346, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h11548, h15341, h15343, h15346, hc01, hc12, hlam, hphi]
              · linarith only [h14484, h15339, h15340, h15341, h15343, h15345, h8811, hc01, hc12, hlam, hphi]
            · linarith only [h14484, h15343, h15344, hc03, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15351 | h15351
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15352 | h15352
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15353 | h15353
                · linarith only [h15341, h15343, h15353, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15355 | h15355
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15356 | h15356
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15357 | h15357
                      · rcases h3bigk with h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c | h15358c
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h7360, hlam, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h11548, hlam, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h14484, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          rcases p15358_3 (m.d 0 3) (by simp) with h15363 | h15363
                          · rcases p15358_3 (m.d 1 3) (by simp) with h15364 | h15364
                            · rcases p15358_3 (m.d 2 3) (by simp) with h15365 | h15365
                              · rcases p15358_3 (m.d 3 4) (by simp) with h15366 | h15366
                                · rcases p15358_3 (m.d 3 5) (by simp) with h15367 | h15367
                                  · linarith only [h15367, hlam, p15358_0]
                                  · rcases h4bigk with h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h8811, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h13831, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h14484, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h13831, h15342, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h8811, hc01, hc14, hlam, hphi, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h13831, h14484, h15342, h15357, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15358_1, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15343, hlam, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      rcases p15369_3 (m.d 0 4) (by simp) with h15379 | h15379
                                      · linarith only [h15379, h8811, hlam]
                                      · linarith only [h15340, h15379, hlam]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h14484, h15357, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15358_1, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15342, hlam, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15353, hlam, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15342, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h14484, h15357, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p15358_1, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h8811, hc01, hc34, hlam, hphi, ht12, ht23, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h0, h13831, hc01, hc34, hlam, hphi, ht12, ht23, p15369_1]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      rcases p15369_3 (m.d 0 4) (by simp) with h15391 | h15391
                                      · linarith only [h14484, h15391, hlam]
                                      · linarith only [h15340, h15391, hlam]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15340, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15352, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15356, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [h15357, hlam, p15369_0]
                                    · have p15369_0 := h15369c.1
                                      have p15369_1 := h15369c.2.1
                                      have p15369_2 := h15369c.2.2.1
                                      have p15369_3 := h15369c.2.2.2
                                      linarith only [hlam, p15369_0]
                                · linarith only [h15357, h15366, hlam]
                              · linarith only [h15355, h15365, hlam]
                            · linarith only [h15351, h15364, hlam]
                          · linarith only [h15363, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15343, hc03, hc34, hlam, hphi, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h0, h11548, h15343, hc01, hc34, hlam, hphi, ht12, ht23, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15343, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          rcases p15358_3 (m.d 0 3) (by simp) with h15407 | h15407
                          · linarith only [h15407, h7360, hlam]
                          · linarith only [h15339, h15407, hlam]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15339, h15341, h15357, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15341, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15353, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          rcases p15358_3 (m.d 0 3) (by simp) with h15414 | h15414
                          · linarith only [h11548, h15414, hlam]
                          · linarith only [h15339, h15414, hlam]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          rcases p15358_3 (m.d 0 3) (by simp) with h15417 | h15417
                          · linarith only [h15417, hlam, p15358_0]
                          · rcases p15358_3 (m.d 1 3) (by simp) with h15419 | h15419
                            · linarith only [h15343, h15419, hlam]
                            · linarith only [h15419, h7360, hlam]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h0, h11548, hc01, hc34, hlam, hphi, ht12, ht23, p15358_1]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          rcases p15358_3 (m.d 0 3) (by simp) with h15425 | h15425
                          · linarith only [h14484, h15425, hlam]
                          · linarith only [h15339, h15425, hlam]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15339, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15351, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15355, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [h15357, hlam, p15358_0]
                        · have p15358_0 := h15358c.1
                          have p15358_1 := h15358c.2.1
                          have p15358_2 := h15358c.2.2.1
                          have p15358_3 := h15358c.2.2.2
                          linarith only [hlam, p15358_0]
                      · linarith only [h15340, h15343, h15357, h8811, hlam]
                    · linarith only [h0, h11548, h13831, h15339, h15340, h15341, h15343, h15356, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11548, h15339, h15355, hlam]
              · linarith only [h13831, h15340, h15342, h15352, h8811, hc01, hc12, hlam, hphi]
            · linarith only [h11548, h15339, h15341, h15351, hlam]
        · linarith only [h0, h11548, h15341, h15342, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15439 | h15439
        · linarith only [h0, h13831, h15341, h15439, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15441 | h15441
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15442 | h15442
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15443 | h15443
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15444 | h15444
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15445 | h15445
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15446 | h15446
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15447 | h15447
                      · rcases h3bigk with h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c | h15448c
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h7360, hlam, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h11548, hlam, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, h15341, h15441, h15447, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          rcases p15448_3 (m.d 0 3) (by simp) with h15454 | h15454
                          · linarith only [h15454, h7360, hlam]
                          · rcases p15448_3 (m.d 1 3) (by simp) with h15456 | h15456
                            · rcases p15448_3 (m.d 2 3) (by simp) with h15457 | h15457
                              · rcases p15448_3 (m.d 3 4) (by simp) with h15458 | h15458
                                · linarith only [h15441, h15458, hlam]
                                · linarith only [h14484, h15458, hlam]
                              · linarith only [h11548, h15457, hlam]
                            · linarith only [h15456, h7360, hlam]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15341, hlam, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, h15341, h7360, hc01, hc23, hlam, hphi, ht12, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, h15339, h15441, hlam, p15448_2]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          rcases p15448_3 (m.d 0 3) (by simp) with h15467 | h15467
                          · linarith only [h11548, h15467, hlam]
                          · rcases p15448_3 (m.d 1 3) (by simp) with h15469 | h15469
                            · linarith only [h15341, h15469, hlam]
                            · linarith only [h15469, h7360, hlam]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, h15339, h15441, h15447, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, h15339, h15447, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h14484, h15339, h15341, h15441, hlam, p15448_2]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15339, h15441, h15447, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p15448_1]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15441, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15444, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          rcases p15448_3 (m.d 0 3) (by simp) with h15480 | h15480
                          · linarith only [h14484, h15480, hlam]
                          · linarith only [h15339, h15480, hlam]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15339, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15442, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15445, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [h15447, hlam, p15448_0]
                        · have p15448_0 := h15448c.1
                          have p15448_1 := h15448c.2.1
                          have p15448_2 := h15448c.2.2.1
                          have p15448_3 := h15448c.2.2.2
                          linarith only [hlam, p15448_0]
                      · linarith only [h14484, h15339, h15340, h15447, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h15439, h15446, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h14484, h15339, h15341, h15441, h15445, hlam]
                · linarith only [h15341, h15441, h15444, hlam]
              · linarith only [h14484, h15339, h15340, h15441, h15443, h8811, hc01, hc13, hlam, hphi]
            · linarith only [h14484, h15339, h15441, h15442, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15494 | h15494
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15495 | h15495
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15496 | h15496
                · linarith only [h0, h15341, h15441, h15496, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15341, h15496, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h14484, h15339, h15340, h15495, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h15339, h15494, h7360, hlam]
    · linarith only [h14484, h15339, h15340, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15502 | h15502
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15503 | h15503
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15504 | h15504
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15505 | h15505
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15506 | h15506
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15507 | h15507
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15508 | h15508
                · linarith only [h0, h11548, h14484, h15503, h15508, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11548, h15505, h15508, hc01, hc13, hlam, hphi]
              · linarith only [h15502, h15507, h8811, hlam]
            · linarith only [h0, h11548, h14484, h15505, h15506, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15513 | h15513
            · linarith only [h0, h11548, h15339, h15505, h15513, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15515 | h15515
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15516 | h15516
                · linarith only [h15505, h15516, h7360, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15518 | h15518
                  · linarith only [h15503, h15513, h15518, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15520 | h15520
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15521 | h15521
                      · rcases h3bigk with h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c | h15522c
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h7360, hlam, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h11548, hlam, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h14484, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15339, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, h15513, h15521, hc01, hc34, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, h15513, h15521, hc01, hc34, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15505, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15513, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, h15503, hc01, hc12, hlam, hphi, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15503, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15516, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15518, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          rcases p15522_3 (m.d 0 3) (by simp) with h15538 | h15538
                          · linarith only [h15538, hlam, p15522_0]
                          · rcases p15522_3 (m.d 1 3) (by simp) with h15540 | h15540
                            · linarith only [h15505, h15540, hlam]
                            · linarith only [h15540, h7360, hlam]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, hc01, hc34, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, h15339, hc01, hc34, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          rcases p15522_3 (m.d 0 3) (by simp) with h15547 | h15547
                          · linarith only [h15547, hlam, p15522_0]
                          · rcases p15522_3 (m.d 1 3) (by simp) with h15549 | h15549
                            · linarith only [h15513, h15549, hlam]
                            · linarith only [h15549, h7360, hlam]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, h15503, hc01, hc35, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h0, h11548, hc01, hc35, hlam, hphi, ht12, ht23, p15522_1]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [h15521, hlam, p15522_0]
                        · have p15522_0 := h15522c.1
                          have p15522_1 := h15522c.2.1
                          have p15522_2 := h15522c.2.2.1
                          have p15522_3 := h15522c.2.2.2
                          linarith only [hlam, p15522_0]
                      · linarith only [h14484, h15502, h15521, hlam]
                    · linarith only [h13831, h15502, h15520, hlam]
              · linarith only [h13831, h15502, h15504, h15515, hlam]
        · linarith only [h0, h11548, h15503, h15504, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15560 | h15560
        · linarith only [h0, h13831, h15503, h15560, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15562 | h15562
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15563 | h15563
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15564 | h15564
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15565 | h15565
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15566 | h15566
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15567 | h15567
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15568 | h15568
                      · rcases h3bigk with h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c | h15569c
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h7360, hlam, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h11548, hlam, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h14484, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15339, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          rcases p15569_3 (m.d 0 3) (by simp) with h15575 | h15575
                          · linarith only [h15575, h7360, hlam]
                          · rcases p15569_3 (m.d 1 3) (by simp) with h15577 | h15577
                            · rcases p15569_3 (m.d 2 3) (by simp) with h15578 | h15578
                              · rcases p15569_3 (m.d 3 4) (by simp) with h15579 | h15579
                                · linarith only [h15562, h15579, hlam]
                                · linarith only [h14484, h15579, hlam]
                              · linarith only [h11548, h15578, hlam]
                            · linarith only [h15577, h7360, hlam]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15503, hlam, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h14484, h15503, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h15339, h15503, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          rcases p15569_3 (m.d 0 3) (by simp) with h15588 | h15588
                          · linarith only [h11548, h15588, hlam]
                          · rcases p15569_3 (m.d 1 3) (by simp) with h15590 | h15590
                            · linarith only [h15503, h15590, hlam]
                            · linarith only [h15590, h7360, hlam]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h15339, h15568, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h15339, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h15562, hc01, hc13, hlam, hphi, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15562, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15565, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h15339, h15503, h15562, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h0, h11548, h15503, h15563, hc01, hc23, hlam, hphi, ht12, p15569_1]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15563, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15566, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [h15568, hlam, p15569_0]
                        · have p15569_0 := h15569c.1
                          have p15569_1 := h15569c.2.1
                          have p15569_2 := h15569c.2.2.1
                          have p15569_3 := h15569c.2.2.2
                          linarith only [hlam, p15569_0]
                      · linarith only [h0, h11548, h13831, h14484, h15502, h15565, h15568, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h14484, h15502, h15503, h15560, h15562, h15567, h8811, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11548, h14484, h15503, h15562, h15566, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h11548, h15339, h15503, h15563, h15565, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h15502, h15564, h8811, hlam]
            · linarith only [h0, h11548, h14484, h15562, h15563, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15613 | h15613
            · linarith only [h0, h11548, h15339, h15562, h15613, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15615 | h15615
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15616 | h15616
                · linarith only [h15562, h15616, h7360, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15503, h15616, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h15502, h15615, h8811, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15620 | h15620
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15621 | h15621
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15622 | h15622
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15623 | h15623
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15624 | h15624
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15625 | h15625
                · linarith only [h0, h11548, h14484, h15620, h15625, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11548, h15622, h15625, hc01, hc13, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15628 | h15628
                · linarith only [h0, h11548, h14484, h15620, h15628, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11548, h15620, h15622, h15628, hc01, hc12, hlam, hphi]
            · linarith only [h0, h11548, h14484, h15622, h15623, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15632 | h15632
            · linarith only [h0, h11548, h15339, h15622, h15632, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15634 | h15634
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15635 | h15635
                · linarith only [h15622, h15635, h7360, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15637 | h15637
                  · linarith only [h0, h11548, h15339, h15620, h15637, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15639 | h15639
                    · linarith only [h0, h11548, h14484, h15502, h15621, h15639, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h13831, h15634, h15639, hc01, hc14, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15642 | h15642
                · linarith only [h0, h11548, h14484, h15620, h15622, h15634, h15642, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15644 | h15644
                  · linarith only [h0, h11548, h15339, h15620, h15622, h15634, h15644, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15646 | h15646
                    · linarith only [h15622, h15634, h15646, h7360, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15648 | h15648
                      · linarith only [h0, h11548, h15620, h15622, h15634, h15648, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h11548, h15620, h15622, h15648, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h11548, h15620, h15621, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15652 | h15652
        · linarith only [h0, h13831, h15620, h15652, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15654 | h15654
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15655 | h15655
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15656 | h15656
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15657 | h15657
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15658 | h15658
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15659 | h15659
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15660 | h15660
                      · linarith only [h0, h11548, h14484, h15502, h15654, h15660, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h11548, h14484, h15656, h15660, hc01, hc14, hlam, hphi]
                    · linarith only [h15652, h15656, h15659, hlam]
                  · linarith only [h15620, h15655, h15658, hlam]
                · linarith only [h0, h11548, h15339, h15620, h15655, h15657, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15666 | h15666
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15667 | h15667
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15668 | h15668
                    · linarith only [h15656, h15668, h8811, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h15652, h15668, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h15620, h15655, h15667, hlam]
                · linarith only [h0, h11548, h15339, h15620, h15654, h15655, h15666, hc01, hc14, hlam, hphi]
            · linarith only [h0, h11548, h14484, h15654, h15655, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15674 | h15674
            · linarith only [h0, h11548, h15339, h15654, h15674, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15676 | h15676
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15677 | h15677
                · linarith only [h15654, h15677, h7360, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15620, h15677, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15680 | h15680
                · linarith only [h0, h15620, h15654, h15680, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h15620, h15680, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h13831 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 4 (by decide) (by decide) with h14484 | h14484
  · exact r1l7_13_24_L_I_H_I_s11_x1_x1_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h13831 h14484
  · exact r1l7_13_24_L_I_H_I_s11_x1_x1_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h13831 h14484

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 2 4 (by decide) (by decide) with h13831 | h13831
  · exact r1l7_13_24_L_I_H_I_s11_x1_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h13831
  · exact r1l7_13_24_L_I_H_I_s11_x1_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h13831

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 2 3 (by decide) (by decide) with h11548 | h11548
  · exact r1l7_13_24_L_I_H_I_s11_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548
  · exact r1l7_13_24_L_I_H_I_s11_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548

end R2N4
