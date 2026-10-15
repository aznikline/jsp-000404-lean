import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h14865 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h14866 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h14867 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 2 3 5 (by decide) (by decide) with h15265 | h15265
  · rcases m.htr 2 4 5 (by decide) (by decide) with h15266 | h15266
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15267 | h15267
      · rcases h1bigk with h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c | h15268c
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h0, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h11385, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h12794, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h13812, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          rcases p15268_3 (m.d 0 1) (by simp) with h15274 | h15274
          · linarith only [h15274, hlam, p15268_0]
          · rcases p15268_3 (m.d 1 2) (by simp) with h15276 | h15276
            · rcases p15268_3 (m.d 1 3) (by simp) with h15277 | h15277
              · linarith only [h14861, h15277, hlam]
              · linarith only [h11385, h15277, hlam]
            · linarith only [h15276, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h11385, hc01, hc12, hlam, hphi, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h12794, hc01, hc12, hlam, hphi, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          rcases p15268_3 (m.d 0 1) (by simp) with h15285 | h15285
          · linarith only [h15285, hlam, p15268_0]
          · rcases p15268_3 (m.d 1 2) (by simp) with h15287 | h15287
            · rcases p15268_3 (m.d 1 3) (by simp) with h15288 | h15288
              · rcases p15268_3 (m.d 1 4) (by simp) with h15289 | h15289
                · linarith only [h14864, h15289, hlam]
                · linarith only [h12794, h15289, hlam]
              · linarith only [h15288, hlam, p15268_0]
            · linarith only [h0, h15287, hlam]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h14861, hlam, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h12794, h14858, h14867, h15265, h15267, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h13812, h14861, hc01, hc12, hlam, hphi, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          rcases p15268_3 (m.d 0 1) (by simp) with h15298 | h15298
          · linarith only [h15298, hlam, p15268_0]
          · rcases p15268_3 (m.d 1 2) (by simp) with h15300 | h15300
            · rcases p15268_3 (m.d 1 3) (by simp) with h15301 | h15301
              · rcases p15268_3 (m.d 1 4) (by simp) with h15302 | h15302
                · rcases p15268_3 (m.d 1 5) (by simp) with h15303 | h15303
                  · linarith only [h14866, h15303, hlam]
                  · linarith only [h13812, h15303, hlam]
                · linarith only [h15302, hlam, p15268_0]
              · linarith only [h11385, h15301, hlam]
            · linarith only [h0, h15300, hlam]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h14862, hlam, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h14864, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h13812, hc01, hc14, hlam, hphi, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          rcases p15268_3 (m.d 0 1) (by simp) with h15313 | h15313
          · linarith only [h15313, hlam, p15268_0]
          · rcases p15268_3 (m.d 1 2) (by simp) with h15315 | h15315
            · rcases p15268_3 (m.d 1 3) (by simp) with h15316 | h15316
              · rcases p15268_3 (m.d 1 4) (by simp) with h15317 | h15317
                · rcases p15268_3 (m.d 1 5) (by simp) with h15318 | h15318
                  · rcases h3bigk with h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c | h15319c
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h11385, hlam, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h15265, h15267, hc03, hc45, hlam, hphi, ht0b, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h11385, h14861, h14867, h15265, h15267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      rcases p15319_3 (m.d 0 3) (by simp) with h15324 | h15324
                      · rcases p15319_3 (m.d 1 3) (by simp) with h15325 | h15325
                        · rcases p15319_3 (m.d 2 3) (by simp) with h15326 | h15326
                          · linarith only [h14856, h15326, hlam]
                          · linarith only [h15265, h15326, hlam]
                        · linarith only [h14865, h15325, hlam]
                      · linarith only [h15324, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14861, h15265, h15267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14861, h14867, h15265, h15267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      rcases p15319_3 (m.d 0 3) (by simp) with h15335 | h15335
                      · linarith only [h11385, h15335, hlam]
                      · linarith only [h14859, h15335, hlam]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14856, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14861, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14867, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14858, h14867, h15267, hc03, hc45, hlam, hphi, ht0b, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14858, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14864, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14858, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h11385, h14858, h14861, h15267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15319_1]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14859, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h14865, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h15265, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [h15267, hlam, p15319_0]
                    · have p15319_0 := h15319c.1
                      have p15319_1 := h15319c.2.1
                      have p15319_2 := h15319c.2.2.1
                      have p15319_3 := h15319c.2.2.2
                      linarith only [hlam, p15319_0]
                  · linarith only [h15318, hlam, p15268_0]
                · linarith only [h12794, h15317, hlam]
              · linarith only [h11385, h15316, hlam]
            · linarith only [h0, h15315, hlam]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h14863, hlam, p15268_1]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h14865, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [h14866, hlam, p15268_0]
        · have p15268_0 := h15268c.1
          have p15268_1 := h15268c.2.1
          have p15268_2 := h15268c.2.2.1
          have p15268_3 := h15268c.2.2.2
          linarith only [hlam, p15268_0]
      · linarith only [h14860, h14867, h15265, h15267, hc04, hc35, hlam, hphi, ht0b, ht5b]
    · linarith only [h14867, h15265, h15266, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h15363 | h15363
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15364 | h15364
      · rcases h1bigk with h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c | h15365c
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h0, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h11385, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h12794, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h13812, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          rcases p15365_3 (m.d 0 1) (by simp) with h15371 | h15371
          · linarith only [h15371, hlam, p15365_0]
          · rcases p15365_3 (m.d 1 2) (by simp) with h15373 | h15373
            · rcases p15365_3 (m.d 1 3) (by simp) with h15374 | h15374
              · linarith only [h14861, h15374, hlam]
              · linarith only [h11385, h15374, hlam]
            · linarith only [h15373, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h11385, hc01, hc12, hlam, hphi, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h12794, hc01, hc12, hlam, hphi, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          rcases p15365_3 (m.d 0 1) (by simp) with h15382 | h15382
          · linarith only [h15382, hlam, p15365_0]
          · rcases p15365_3 (m.d 1 2) (by simp) with h15384 | h15384
            · rcases p15365_3 (m.d 1 3) (by simp) with h15385 | h15385
              · rcases p15365_3 (m.d 1 4) (by simp) with h15386 | h15386
                · linarith only [h14864, h15386, hlam]
                · linarith only [h12794, h15386, hlam]
              · linarith only [h15385, hlam, p15365_0]
            · linarith only [h0, h15384, hlam]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h14861, hlam, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h13812, h14866, hc01, hc13, hlam, hphi, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h13812, h14861, hc01, hc12, hlam, hphi, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          rcases p15365_3 (m.d 0 1) (by simp) with h15395 | h15395
          · linarith only [h15395, hlam, p15365_0]
          · rcases p15365_3 (m.d 1 2) (by simp) with h15397 | h15397
            · rcases p15365_3 (m.d 1 3) (by simp) with h15398 | h15398
              · rcases p15365_3 (m.d 1 4) (by simp) with h15399 | h15399
                · rcases p15365_3 (m.d 1 5) (by simp) with h15400 | h15400
                  · linarith only [h14866, h15400, hlam]
                  · linarith only [h13812, h15400, hlam]
                · linarith only [h15399, hlam, p15365_0]
              · linarith only [h11385, h15398, hlam]
            · linarith only [h0, h15397, hlam]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h14862, hlam, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h14864, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h13812, hc01, hc14, hlam, hphi, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          rcases p15365_3 (m.d 0 1) (by simp) with h15410 | h15410
          · linarith only [h15410, hlam, p15365_0]
          · rcases p15365_3 (m.d 1 2) (by simp) with h15412 | h15412
            · rcases p15365_3 (m.d 1 3) (by simp) with h15413 | h15413
              · rcases p15365_3 (m.d 1 4) (by simp) with h15414 | h15414
                · rcases p15365_3 (m.d 1 5) (by simp) with h15415 | h15415
                  · rcases h3bigk with h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c | h15416c
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h11385, hlam, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      rcases p15416_3 (m.d 0 3) (by simp) with h15419 | h15419
                      · rcases p15416_3 (m.d 1 3) (by simp) with h15420 | h15420
                        · rcases p15416_3 (m.d 2 3) (by simp) with h15421 | h15421
                          · linarith only [h14856, h15421, hlam]
                          · rcases p15416_3 (m.d 3 4) (by simp) with h15423 | h15423
                            · linarith only [h14858, h15423, hlam]
                            · linarith only [h14867, h15423, hlam]
                        · linarith only [h14861, h15420, hlam]
                      · linarith only [h14856, h15419, hlam]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h11385, h14861, h14867, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h11385, h14861, h15265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      rcases p15416_3 (m.d 0 3) (by simp) with h15432 | h15432
                      · linarith only [h11385, h15432, hlam]
                      · linarith only [h14856, h15432, hlam]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14861, h15265, h15364, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14861, h15265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14856, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14861, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14867, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h15265, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14858, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14864, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14858, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h11385, h14858, h14861, h15265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14859, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h14865, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p15416_1]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [h15364, hlam, p15416_0]
                    · have p15416_0 := h15416c.1
                      have p15416_1 := h15416c.2.1
                      have p15416_2 := h15416c.2.2.1
                      have p15416_3 := h15416c.2.2.2
                      linarith only [hlam, p15416_0]
                  · linarith only [h15415, hlam, p15365_0]
                · linarith only [h12794, h15414, hlam]
              · linarith only [h11385, h15413, hlam]
            · linarith only [h0, h15412, hlam]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h14863, hlam, p15365_1]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h14865, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [h14866, hlam, p15365_0]
        · have p15365_0 := h15365c.1
          have p15365_1 := h15365c.2.1
          have p15365_2 := h15365c.2.2.1
          have p15365_3 := h15365c.2.2.2
          linarith only [hlam, p15365_0]
      · linarith only [h0, h14857, h14867, h15363, h15364, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15461 | h15461
      · rcases h1bigk with h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c | h15462c
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h0, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h11385, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h12794, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h13812, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          rcases p15462_3 (m.d 0 1) (by simp) with h15468 | h15468
          · linarith only [h15468, hlam, p15462_0]
          · rcases p15462_3 (m.d 1 2) (by simp) with h15470 | h15470
            · rcases p15462_3 (m.d 1 3) (by simp) with h15471 | h15471
              · linarith only [h14861, h15471, hlam]
              · linarith only [h11385, h15471, hlam]
            · linarith only [h15470, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h11385, h14858, h15363, h15461, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h12794, hc01, hc12, hlam, hphi, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          rcases p15462_3 (m.d 0 1) (by simp) with h15479 | h15479
          · linarith only [h15479, hlam, p15462_0]
          · rcases p15462_3 (m.d 1 2) (by simp) with h15481 | h15481
            · rcases p15462_3 (m.d 1 3) (by simp) with h15482 | h15482
              · rcases p15462_3 (m.d 1 4) (by simp) with h15483 | h15483
                · linarith only [h14864, h15483, hlam]
                · linarith only [h12794, h15483, hlam]
              · linarith only [h15482, hlam, p15462_0]
            · linarith only [h0, h15481, hlam]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h14861, hlam, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h12794, h14858, h14867, h15363, h15461, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h13812, h14861, hc01, hc12, hlam, hphi, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          rcases p15462_3 (m.d 0 1) (by simp) with h15492 | h15492
          · linarith only [h15492, hlam, p15462_0]
          · rcases p15462_3 (m.d 1 2) (by simp) with h15494 | h15494
            · rcases p15462_3 (m.d 1 3) (by simp) with h15495 | h15495
              · rcases p15462_3 (m.d 1 4) (by simp) with h15496 | h15496
                · rcases p15462_3 (m.d 1 5) (by simp) with h15497 | h15497
                  · linarith only [h14866, h15497, hlam]
                  · linarith only [h13812, h15497, hlam]
                · linarith only [h15496, hlam, p15462_0]
              · linarith only [h11385, h15495, hlam]
            · linarith only [h0, h15494, hlam]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h14862, hlam, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h14864, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h13812, hc01, hc14, hlam, hphi, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          rcases p15462_3 (m.d 0 1) (by simp) with h15507 | h15507
          · linarith only [h15507, hlam, p15462_0]
          · rcases p15462_3 (m.d 1 2) (by simp) with h15509 | h15509
            · rcases p15462_3 (m.d 1 3) (by simp) with h15510 | h15510
              · rcases p15462_3 (m.d 1 4) (by simp) with h15511 | h15511
                · rcases p15462_3 (m.d 1 5) (by simp) with h15512 | h15512
                  · rcases h3bigk with h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c | h15513c
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h11385, hlam, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      rcases p15513_3 (m.d 0 3) (by simp) with h15516 | h15516
                      · rcases p15513_3 (m.d 1 3) (by simp) with h15517 | h15517
                        · rcases p15513_3 (m.d 2 3) (by simp) with h15518 | h15518
                          · linarith only [h14856, h15518, hlam]
                          · rcases p15513_3 (m.d 3 4) (by simp) with h15520 | h15520
                            · linarith only [h14858, h15520, hlam]
                            · linarith only [h14867, h15520, hlam]
                        · linarith only [h14861, h15517, hlam]
                      · linarith only [h14856, h15516, hlam]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h11385, h14861, h14867, h15363, h15461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h11385, h14861, h15265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      rcases p15513_3 (m.d 0 3) (by simp) with h15529 | h15529
                      · linarith only [h11385, h15529, hlam]
                      · linarith only [h14856, h15529, hlam]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14861, h14867, h15363, h15461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14861, h14867, h15363, h15461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14856, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14861, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14867, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h15265, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14858, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14864, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14858, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h11385, h14858, h14861, h14867, h15363, h15461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14859, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h14865, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p15513_1]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [h15461, hlam, p15513_0]
                    · have p15513_0 := h15513c.1
                      have p15513_1 := h15513c.2.1
                      have p15513_2 := h15513c.2.2.1
                      have p15513_3 := h15513c.2.2.2
                      linarith only [hlam, p15513_0]
                  · linarith only [h15512, hlam, p15462_0]
                · linarith only [h12794, h15511, hlam]
              · linarith only [h11385, h15510, hlam]
            · linarith only [h0, h15509, hlam]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h14863, hlam, p15462_1]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h14865, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [h14866, hlam, p15462_0]
        · have p15462_0 := h15462c.1
          have p15462_1 := h15462c.2.1
          have p15462_2 := h15462c.2.2.1
          have p15462_3 := h15462c.2.2.2
          linarith only [hlam, p15462_0]
      · rcases h1bigk with h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c | h15557c
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h0, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h11385, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h12794, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h13812, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          rcases p15557_3 (m.d 0 1) (by simp) with h15563 | h15563
          · linarith only [h15563, hlam, p15557_0]
          · rcases p15557_3 (m.d 1 2) (by simp) with h15565 | h15565
            · rcases p15557_3 (m.d 1 3) (by simp) with h15566 | h15566
              · linarith only [h14861, h15566, hlam]
              · linarith only [h11385, h15566, hlam]
            · linarith only [h15565, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h12794, h14860, h14864, h15461, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h12794, h14860, h15461, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          rcases p15557_3 (m.d 0 1) (by simp) with h15574 | h15574
          · linarith only [h15574, hlam, p15557_0]
          · rcases p15557_3 (m.d 1 2) (by simp) with h15576 | h15576
            · rcases p15557_3 (m.d 1 3) (by simp) with h15577 | h15577
              · rcases p15557_3 (m.d 1 4) (by simp) with h15578 | h15578
                · linarith only [h14864, h15578, hlam]
                · linarith only [h12794, h15578, hlam]
              · linarith only [h15577, hlam, p15557_0]
            · linarith only [h0, h15576, hlam]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h14861, hlam, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h12794, h14860, h14867, h15461, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h13812, h14860, h14861, h14867, h15461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          rcases p15557_3 (m.d 0 1) (by simp) with h15587 | h15587
          · linarith only [h15587, hlam, p15557_0]
          · rcases p15557_3 (m.d 1 2) (by simp) with h15589 | h15589
            · rcases p15557_3 (m.d 1 3) (by simp) with h15590 | h15590
              · rcases p15557_3 (m.d 1 4) (by simp) with h15591 | h15591
                · rcases p15557_3 (m.d 1 5) (by simp) with h15592 | h15592
                  · linarith only [h14866, h15592, hlam]
                  · linarith only [h13812, h15592, hlam]
                · linarith only [h15591, hlam, p15557_0]
              · linarith only [h11385, h15590, hlam]
            · linarith only [h0, h15589, hlam]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h14862, hlam, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h14864, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h13812, h14860, h14867, h15461, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          rcases p15557_3 (m.d 0 1) (by simp) with h15602 | h15602
          · linarith only [h15602, hlam, p15557_0]
          · rcases p15557_3 (m.d 1 2) (by simp) with h15604 | h15604
            · rcases p15557_3 (m.d 1 3) (by simp) with h15605 | h15605
              · rcases p15557_3 (m.d 1 4) (by simp) with h15606 | h15606
                · rcases p15557_3 (m.d 1 5) (by simp) with h15607 | h15607
                  · rcases h3bigk with h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c | h15608c
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h11385, hlam, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      rcases p15608_3 (m.d 0 3) (by simp) with h15611 | h15611
                      · rcases p15608_3 (m.d 1 3) (by simp) with h15612 | h15612
                        · rcases p15608_3 (m.d 2 3) (by simp) with h15613 | h15613
                          · linarith only [h14856, h15613, hlam]
                          · rcases p15608_3 (m.d 3 4) (by simp) with h15615 | h15615
                            · linarith only [h14858, h15615, hlam]
                            · linarith only [h14867, h15615, hlam]
                        · linarith only [h14861, h15612, hlam]
                      · linarith only [h14856, h15611, hlam]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14867, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h11385, h14861, h15265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      rcases p15608_3 (m.d 0 3) (by simp) with h15624 | h15624
                      · linarith only [h11385, h15624, hlam]
                      · linarith only [h14856, h15624, hlam]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14861, h14867, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14861, h14867, h15461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14856, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14861, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14867, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h15265, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14858, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14864, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14858, h14860, h15461, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h15461, hlam, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14859, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h14865, hlam, p15608_0]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [h11385, h14858, h14860, h14861, h15461, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15608_1]
                    · have p15608_0 := h15608c.1
                      have p15608_1 := h15608c.2.1
                      have p15608_2 := h15608c.2.2.1
                      have p15608_3 := h15608c.2.2.2
                      linarith only [hlam, p15608_0]
                  · linarith only [h15607, hlam, p15557_0]
                · linarith only [h12794, h15606, hlam]
              · linarith only [h11385, h15605, hlam]
            · linarith only [h0, h15604, hlam]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h14863, hlam, p15557_1]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h14865, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [h14866, hlam, p15557_0]
        · have p15557_0 := h15557c.1
          have p15557_1 := h15557c.2.1
          have p15557_2 := h15557c.2.2.1
          have p15557_3 := h15557c.2.2.2
          linarith only [hlam, p15557_0]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h14865 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h14866 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 2 3 4 (by decide) (by decide) with h14867 | h14867
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864 h14865 h14866 h14867
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864 h14865 h14866 h14867

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h14865 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h14866 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  linarith only [h11385, h12794, h14858, h14860, h14861, h14866, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h14865 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 4 5 (by decide) (by decide) with h14866 | h14866
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864 h14865 h14866
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864 h14865 h14866

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h14865 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  linarith only [h11385, h14859, h14865, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 3 5 (by decide) (by decide) with h14865 | h14865
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864 h14865
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864 h14865

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  linarith only [h11385, h14858, h14864, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 3 4 (by decide) (by decide) with h14864 | h14864
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863 h14864

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 3 4 (by decide) (by decide) with h15655 | h15655
  · rcases m.htr 1 3 5 (by decide) (by decide) with h15656 | h15656
    · linarith only [h14861, h14863, h15656, hlam]
    · linarith only [h11385, h14859, h15656, hlam]
  · linarith only [h11385, h14858, h15655, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 2 5 (by decide) (by decide) with h14863 | h14863
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862 h14863

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  linarith only [h0, h14857, h14862, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 2 4 (by decide) (by decide) with h14862 | h14862
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861 h14862

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  linarith only [h0, h14856, h14861, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 2 3 (by decide) (by decide) with h14861 | h14861
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860 h14861

end R2N4
