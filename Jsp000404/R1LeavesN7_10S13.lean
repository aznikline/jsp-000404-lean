import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8894 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8895 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h8896 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 2 3 5 (by decide) (by decide) with h9361 | h9361
  · rcases m.htr 2 4 5 (by decide) (by decide) with h9362 | h9362
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9363 | h9363
      · rcases h2bigk with h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h0, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9367 | h9367
          · rcases p9364_3 (m.d 1 2) (by simp) with h9368 | h9368
            · rcases p9364_3 (m.d 2 3) (by simp) with h9369 | h9369
              · linarith only [h9369, hlam, p9364_0]
              · rcases p9364_3 (m.d 2 4) (by simp) with h9371 | h9371
                · linarith only [h8887, h9371, hlam]
                · linarith only [h8896, h9371, hlam]
            · linarith only [h8891, h9368, hlam]
          · linarith only [h9367, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9376 | h9376
          · rcases p9364_3 (m.d 1 2) (by simp) with h9377 | h9377
            · rcases p9364_3 (m.d 2 3) (by simp) with h9378 | h9378
              · linarith only [h8886, h9378, hlam]
              · rcases p9364_3 (m.d 2 4) (by simp) with h9380 | h9380
                · linarith only [h9380, hlam, p9364_0]
                · rcases p9364_3 (m.d 2 5) (by simp) with h9382 | h9382
                  · linarith only [h8888, h9382, hlam]
                  · rcases h4bigk with h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c | h9384c
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h6874, hlam, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8887, hlam, p9364_2, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h6874, h8891, h8894, h8896, h9361, h9363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      rcases p9384_3 (m.d 0 4) (by simp) with h9389 | h9389
                      · rcases p9384_3 (m.d 1 4) (by simp) with h9390 | h9390
                        · rcases p9384_3 (m.d 2 4) (by simp) with h9391 | h9391
                          · linarith only [h8887, h9391, hlam]
                          · linarith only [h9362, h9391, hlam]
                        · linarith only [h8895, h9390, hlam]
                      · linarith only [h9389, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8891, h8894, h8896, h9361, h9363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8891, h8894, h8896, h9361, h9363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      rcases p9384_3 (m.d 0 4) (by simp) with h9400 | h9400
                      · linarith only [h6874, h9400, hlam]
                      · linarith only [h8890, h9400, hlam]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8887, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8892, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8896, hlam, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p9364_1, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8889, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8894, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8889, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h0, h8886, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9384_1]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8890, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h8895, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h9362, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [h9363, hlam, p9384_0]
                    · have p9384_0 := h9384c.1
                      have p9384_1 := h9384c.2.1
                      have p9384_2 := h9384c.2.2.1
                      have p9384_3 := h9384c.2.2.2
                      linarith only [hlam, p9384_0]
            · linarith only [h8892, h9377, hlam]
          · linarith only [h9376, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9420 | h9420
          · rcases p9364_3 (m.d 1 2) (by simp) with h9421 | h9421
            · rcases p9364_3 (m.d 2 3) (by simp) with h9422 | h9422
              · linarith only [h8886, h9422, hlam]
              · linarith only [h9361, h9422, hlam]
            · linarith only [h8893, h9421, hlam]
          · linarith only [h9420, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8886, h9361, h9363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9364_1]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9429 | h9429
          · linarith only [h0, h9429, hlam]
          · linarith only [h8886, h9429, hlam]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9432 | h9432
          · linarith only [h0, h9432, hlam]
          · linarith only [h8887, h9432, hlam]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9435 | h9435
          · linarith only [h0, h9435, hlam]
          · linarith only [h8888, h9435, hlam]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8886, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8891, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8896, hlam, p9364_1]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8886, h8889, h8896, hc02, hc25, hlam, hphi, ht0b, ht5b, p9364_1]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8887, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8892, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h0, h8886, h8889, h8896, h9361, h9363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9364_1]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          rcases p9364_3 (m.d 0 2) (by simp) with h9447 | h9447
          · rcases p9364_3 (m.d 1 2) (by simp) with h9448 | h9448
            · rcases p9364_3 (m.d 2 3) (by simp) with h9449 | h9449
              · linarith only [h8896, h9449, hlam]
              · linarith only [h9361, h9449, hlam]
            · linarith only [h8893, h9448, hlam]
          · linarith only [h8888, h9447, hlam]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8888, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h8893, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h9361, hlam, p9364_0]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [h9362, hlam, p9364_1]
        · have p9364_0 := h9364c.1
          have p9364_1 := h9364c.2.1
          have p9364_2 := h9364c.2.2.1
          have p9364_3 := h9364c.2.2.2
          linarith only [hlam, p9364_0]
      · linarith only [h8890, h8896, h9361, h9363, hc04, hc35, hlam, hphi, ht0b, ht5b]
    · linarith only [h8896, h9361, h9362, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h9461 | h9461
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9462 | h9462
      · rcases h2bigk with h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c | h9463c
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h0, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9466 | h9466
          · rcases p9463_3 (m.d 1 2) (by simp) with h9467 | h9467
            · rcases p9463_3 (m.d 2 3) (by simp) with h9468 | h9468
              · linarith only [h9468, hlam, p9463_0]
              · rcases p9463_3 (m.d 2 4) (by simp) with h9470 | h9470
                · linarith only [h8887, h9470, hlam]
                · linarith only [h8896, h9470, hlam]
            · linarith only [h8891, h9467, hlam]
          · linarith only [h9466, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9475 | h9475
          · rcases p9463_3 (m.d 1 2) (by simp) with h9476 | h9476
            · rcases p9463_3 (m.d 2 3) (by simp) with h9477 | h9477
              · linarith only [h8886, h9477, hlam]
              · rcases p9463_3 (m.d 2 4) (by simp) with h9479 | h9479
                · linarith only [h9479, hlam, p9463_0]
                · rcases p9463_3 (m.d 2 5) (by simp) with h9481 | h9481
                  · linarith only [h8888, h9481, hlam]
                  · rcases h4bigk with h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c | h9483c
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h6874, hlam, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h6874, h8891, h8894, h9461, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h6874, h8891, h8894, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      rcases p9483_3 (m.d 0 4) (by simp) with h9488 | h9488
                      · rcases p9483_3 (m.d 1 4) (by simp) with h9489 | h9489
                        · rcases p9483_3 (m.d 2 4) (by simp) with h9490 | h9490
                          · linarith only [h8887, h9490, hlam]
                          · linarith only [h9461, h9490, hlam]
                        · linarith only [h8895, h9489, hlam]
                      · linarith only [h9488, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8891, h8894, h9461, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8891, h8894, h9361, h9462, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      rcases p9483_3 (m.d 0 4) (by simp) with h9499 | h9499
                      · linarith only [h6874, h9499, hlam]
                      · linarith only [h8890, h9499, hlam]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8887, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8892, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8896, hlam, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9463_1, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8889, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8894, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8887, h8889, hlam, p9463_2, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h0, h8886, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9483_1]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8890, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h8895, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h9461, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [h9462, hlam, p9483_0]
                    · have p9483_0 := h9483c.1
                      have p9483_1 := h9483c.2.1
                      have p9483_2 := h9483c.2.2.1
                      have p9483_3 := h9483c.2.2.2
                      linarith only [hlam, p9483_0]
            · linarith only [h8892, h9476, hlam]
          · linarith only [h9475, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9519 | h9519
          · rcases p9463_3 (m.d 1 2) (by simp) with h9520 | h9520
            · rcases p9463_3 (m.d 2 3) (by simp) with h9521 | h9521
              · linarith only [h8886, h9521, hlam]
              · rcases p9463_3 (m.d 2 4) (by simp) with h9523 | h9523
                · linarith only [h8887, h9523, hlam]
                · linarith only [h9461, h9523, hlam]
            · linarith only [h8893, h9520, hlam]
          · linarith only [h9519, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8887, h9461, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9463_1]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9530 | h9530
          · linarith only [h0, h9530, hlam]
          · linarith only [h8886, h9530, hlam]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9533 | h9533
          · linarith only [h0, h9533, hlam]
          · linarith only [h8887, h9533, hlam]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9536 | h9536
          · linarith only [h0, h9536, hlam]
          · linarith only [h8888, h9536, hlam]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8886, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8891, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8896, hlam, p9463_1]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h9361, hlam, p9463_1]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8887, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8892, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9546 | h9546
          · rcases p9463_3 (m.d 1 2) (by simp) with h9547 | h9547
            · rcases p9463_3 (m.d 2 3) (by simp) with h9548 | h9548
              · linarith only [h8896, h9548, hlam]
              · rcases p9463_3 (m.d 2 4) (by simp) with h9550 | h9550
                · rcases p9463_3 (m.d 2 5) (by simp) with h9551 | h9551
                  · linarith only [h9461, h9551, hlam]
                  · linarith only [h9361, h9551, hlam]
                · linarith only [h8896, h9550, hlam]
            · linarith only [h8891, h9547, hlam]
          · linarith only [h8886, h9546, hlam]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9558 | h9558
          · rcases p9463_3 (m.d 1 2) (by simp) with h9559 | h9559
            · rcases p9463_3 (m.d 2 3) (by simp) with h9560 | h9560
              · linarith only [h8896, h9560, hlam]
              · rcases p9463_3 (m.d 2 4) (by simp) with h9562 | h9562
                · rcases p9463_3 (m.d 2 5) (by simp) with h9563 | h9563
                  · linarith only [h9461, h9563, hlam]
                  · rcases h4bigk with h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c | h9565c
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h6874, hlam, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h9361, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9463_1, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h6874, h8891, h8894, h8896, h9361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9463_1, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      rcases p9565_3 (m.d 0 4) (by simp) with h9570 | h9570
                      · rcases p9565_3 (m.d 1 4) (by simp) with h9571 | h9571
                        · rcases p9565_3 (m.d 2 4) (by simp) with h9572 | h9572
                          · linarith only [h8887, h9572, hlam]
                          · linarith only [h9461, h9572, hlam]
                        · linarith only [h8895, h9571, hlam]
                      · linarith only [h9570, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8891, h8894, h9361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9463_1, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8891, h8894, h8896, h9361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9463_1, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      rcases p9565_3 (m.d 0 4) (by simp) with h9581 | h9581
                      · linarith only [h6874, h9581, hlam]
                      · linarith only [h8890, h9581, hlam]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8887, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8892, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8896, hlam, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8886, h8889, h8896, hc02, hc45, hlam, hphi, ht0b, ht5b, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8889, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8894, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8886, h8889, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h0, h8886, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9565_1]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8890, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h8895, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h9461, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [h9462, hlam, p9565_0]
                    · have p9565_0 := h9565c.1
                      have p9565_1 := h9565c.2.1
                      have p9565_2 := h9565c.2.2.1
                      have p9565_3 := h9565c.2.2.2
                      linarith only [hlam, p9565_0]
                · linarith only [h9461, h9562, hlam]
            · linarith only [h8893, h9559, hlam]
          · linarith only [h8888, h9558, hlam]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8888, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h8893, hlam, p9463_0]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          rcases p9463_3 (m.d 0 2) (by simp) with h9604 | h9604
          · rcases p9463_3 (m.d 1 2) (by simp) with h9605 | h9605
            · rcases p9463_3 (m.d 2 3) (by simp) with h9606 | h9606
              · linarith only [h9361, h9606, hlam]
              · rcases p9463_3 (m.d 2 4) (by simp) with h9608 | h9608
                · rcases p9463_3 (m.d 2 5) (by simp) with h9609 | h9609
                  · rcases h4bigk with h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c | h9610c
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h6874, hlam, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h6874, h8891, h8894, h9461, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h6874, h8891, h8894, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      rcases p9610_3 (m.d 0 4) (by simp) with h9615 | h9615
                      · rcases p9610_3 (m.d 1 4) (by simp) with h9616 | h9616
                        · rcases p9610_3 (m.d 2 4) (by simp) with h9617 | h9617
                          · linarith only [h8887, h9617, hlam]
                          · linarith only [h9461, h9617, hlam]
                        · linarith only [h8895, h9616, hlam]
                      · linarith only [h9615, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8891, h8894, h9461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9463_1, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8891, h8894, h8896, h9461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9463_1, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      rcases p9610_3 (m.d 0 4) (by simp) with h9626 | h9626
                      · linarith only [h6874, h9626, hlam]
                      · linarith only [h8890, h9626, hlam]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8887, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8892, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8896, hlam, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h0, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8889, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8894, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h0, h8886, h8889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h0, h8886, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9610_1]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8890, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h8895, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h9461, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [h9462, hlam, p9610_0]
                    · have p9610_0 := h9610c.1
                      have p9610_1 := h9610c.2.1
                      have p9610_2 := h9610c.2.2.1
                      have p9610_3 := h9610c.2.2.2
                      linarith only [hlam, p9610_0]
                  · linarith only [h9361, h9609, hlam]
                · linarith only [h8896, h9608, hlam]
            · linarith only [h8891, h9605, hlam]
          · linarith only [h8886, h9604, hlam]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [h9461, hlam, p9463_1]
        · have p9463_0 := h9463c.1
          have p9463_1 := h9463c.2.1
          have p9463_2 := h9463c.2.2.1
          have p9463_3 := h9463c.2.2.2
          linarith only [hlam, p9463_0]
      · linarith only [h8896, h9461, h9462, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9651 | h9651
      · rcases h2bigk with h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c | h9652c
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h0, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8886, h8889, h8896, h9461, h9651, hlam, p9652_2]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8886, h8889, h9461, h9651, hlam, p9652_2]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          rcases p9652_3 (m.d 0 2) (by simp) with h9657 | h9657
          · rcases p9652_3 (m.d 1 2) (by simp) with h9658 | h9658
            · rcases p9652_3 (m.d 2 3) (by simp) with h9659 | h9659
              · linarith only [h8886, h9659, hlam]
              · rcases p9652_3 (m.d 2 4) (by simp) with h9661 | h9661
                · linarith only [h8887, h9661, hlam]
                · rcases p9652_3 (m.d 2 5) (by simp) with h9663 | h9663
                  · linarith only [h9663, hlam, p9652_0]
                  · rcases h4bigk with h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c | h9665c
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h6874, hlam, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      rcases p9665_3 (m.d 0 4) (by simp) with h9668 | h9668
                      · rcases p9665_3 (m.d 1 4) (by simp) with h9669 | h9669
                        · rcases p9665_3 (m.d 2 4) (by simp) with h9670 | h9670
                          · linarith only [h8887, h9670, hlam]
                          · rcases p9665_3 (m.d 3 4) (by simp) with h9672 | h9672
                            · linarith only [h8889, h9672, hlam]
                            · linarith only [h8896, h9672, hlam]
                        · linarith only [h8892, h9669, hlam]
                      · linarith only [h8887, h9668, hlam]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h6874, h8891, h8894, h9651, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h6874, h8891, h8894, h9461, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      rcases p9665_3 (m.d 0 4) (by simp) with h9681 | h9681
                      · linarith only [h6874, h9681, hlam]
                      · linarith only [h8887, h9681, hlam]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8891, h8894, h8896, h9461, h9651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8891, h8894, h8896, h9461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8887, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8892, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8896, hlam, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h9461, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8889, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8894, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8896, hc23, hc34, hlam, hphi, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h0, h8886, h8889, h8896, h9461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8890, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8895, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h8896, h9651, hc23, hc35, hlam, hphi, p9665_1]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [h9651, hlam, p9665_0]
                    · have p9665_0 := h9665c.1
                      have p9665_1 := h9665c.2.1
                      have p9665_2 := h9665c.2.2.1
                      have p9665_3 := h9665c.2.2.2
                      linarith only [hlam, p9665_0]
            · linarith only [h8893, h9658, hlam]
          · linarith only [h9657, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8886, h8889, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9652_1]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h0, h8886, h8889, h8896, h9461, h9651, hlam, p9652_2]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h0, h8886, h8889, h9461, h9651, hlam, p9652_2]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          rcases p9652_3 (m.d 0 2) (by simp) with h9707 | h9707
          · linarith only [h0, h9707, hlam]
          · linarith only [h8888, h9707, hlam]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8886, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8891, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8896, hlam, p9652_1]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h9361, hlam, p9652_1]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8887, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8892, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h0, h8886, h8889, h9461, h9651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9652_1]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h9461, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8888, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h8893, hlam, p9652_0]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h0, h8886, h8889, h9461, h9651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9652_1]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [h0, h8886, h8889, h9461, h9651, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9652_1]
        · have p9652_0 := h9652c.1
          have p9652_1 := h9652c.2.1
          have p9652_2 := h9652c.2.2.1
          have p9652_3 := h9652c.2.2.2
          linarith only [hlam, p9652_0]
      · rcases h2bigk with h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c | h9725c
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h0, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8886, h8889, h8890, h8896, h9651, hlam, p9725_2]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          rcases p9725_3 (m.d 0 2) (by simp) with h9729 | h9729
          · rcases p9725_3 (m.d 1 2) (by simp) with h9730 | h9730
            · rcases p9725_3 (m.d 2 3) (by simp) with h9731 | h9731
              · linarith only [h8886, h9731, hlam]
              · rcases p9725_3 (m.d 2 4) (by simp) with h9733 | h9733
                · linarith only [h9733, hlam, p9725_0]
                · rcases p9725_3 (m.d 2 5) (by simp) with h9735 | h9735
                  · linarith only [h8888, h9735, hlam]
                  · linarith only [h9461, h9735, hlam]
            · linarith only [h8892, h9730, hlam]
          · linarith only [h9729, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          rcases p9725_3 (m.d 0 2) (by simp) with h9740 | h9740
          · rcases p9725_3 (m.d 1 2) (by simp) with h9741 | h9741
            · rcases p9725_3 (m.d 2 3) (by simp) with h9742 | h9742
              · linarith only [h8886, h9742, hlam]
              · rcases p9725_3 (m.d 2 4) (by simp) with h9744 | h9744
                · linarith only [h8887, h9744, hlam]
                · rcases p9725_3 (m.d 2 5) (by simp) with h9746 | h9746
                  · linarith only [h9746, hlam, p9725_0]
                  · rcases h4bigk with h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h6874, hlam, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      rcases p9748_3 (m.d 0 4) (by simp) with h9751 | h9751
                      · rcases p9748_3 (m.d 1 4) (by simp) with h9752 | h9752
                        · rcases p9748_3 (m.d 2 4) (by simp) with h9753 | h9753
                          · linarith only [h8887, h9753, hlam]
                          · rcases p9748_3 (m.d 3 4) (by simp) with h9755 | h9755
                            · linarith only [h8889, h9755, hlam]
                            · linarith only [h8896, h9755, hlam]
                        · linarith only [h8892, h9752, hlam]
                      · linarith only [h8887, h9751, hlam]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8886, h8889, h8896, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h0, h8886, h8889, h8896, h9651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      rcases p9748_3 (m.d 0 4) (by simp) with h9764 | h9764
                      · linarith only [h6874, h9764, hlam]
                      · linarith only [h8887, h9764, hlam]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8891, h8894, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8891, h8894, h8896, h9651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8887, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8892, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8896, hlam, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h9461, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8889, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8894, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8890, h8896, h9651, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h9651, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8890, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h8895, hlam, p9748_0]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9748_1]
                    · have p9748_0 := h9748c.1
                      have p9748_1 := h9748c.2.1
                      have p9748_2 := h9748c.2.2.1
                      have p9748_3 := h9748c.2.2.2
                      linarith only [hlam, p9748_0]
            · linarith only [h8893, h9741, hlam]
          · linarith only [h9740, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8886, h8889, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9725_1]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h0, h8886, h8889, h8890, h8896, h9651, hlam, p9725_2]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          rcases p9725_3 (m.d 0 2) (by simp) with h9789 | h9789
          · linarith only [h0, h9789, hlam]
          · linarith only [h8887, h9789, hlam]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          rcases p9725_3 (m.d 0 2) (by simp) with h9792 | h9792
          · linarith only [h0, h9792, hlam]
          · linarith only [h8888, h9792, hlam]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8886, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8891, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8896, hlam, p9725_1]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h9361, hlam, p9725_1]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8887, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8892, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8886, h8889, h8890, h8896, h9651, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9725_1]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h9461, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8888, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [h8893, hlam, p9725_0]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          rcases p9725_3 (m.d 0 2) (by simp) with h9807 | h9807
          · rcases p9725_3 (m.d 1 2) (by simp) with h9808 | h9808
            · rcases p9725_3 (m.d 2 3) (by simp) with h9809 | h9809
              · linarith only [h9361, h9809, hlam]
              · rcases p9725_3 (m.d 2 4) (by simp) with h9811 | h9811
                · linarith only [h9461, h9811, hlam]
                · linarith only [h8896, h9811, hlam]
            · linarith only [h8891, h9808, hlam]
          · linarith only [h8886, h9807, hlam]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          rcases p9725_3 (m.d 0 2) (by simp) with h9816 | h9816
          · rcases p9725_3 (m.d 1 2) (by simp) with h9817 | h9817
            · rcases p9725_3 (m.d 2 3) (by simp) with h9818 | h9818
              · linarith only [h9361, h9818, hlam]
              · rcases p9725_3 (m.d 2 4) (by simp) with h9820 | h9820
                · linarith only [h9461, h9820, hlam]
                · rcases p9725_3 (m.d 2 5) (by simp) with h9822 | h9822
                  · rcases h4bigk with h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c | h9823c
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h6874, hlam, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      rcases p9823_3 (m.d 0 4) (by simp) with h9826 | h9826
                      · rcases p9823_3 (m.d 1 4) (by simp) with h9827 | h9827
                        · rcases p9823_3 (m.d 2 4) (by simp) with h9828 | h9828
                          · linarith only [h8887, h9828, hlam]
                          · rcases p9823_3 (m.d 3 4) (by simp) with h9830 | h9830
                            · linarith only [h8889, h9830, hlam]
                            · linarith only [h8896, h9830, hlam]
                        · linarith only [h8892, h9827, hlam]
                      · linarith only [h8887, h9826, hlam]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h0, h8886, h8889, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h0, h8886, h8889, h8896, h9461, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h6874, h8891, h8894, hc01, hc12, hlam, hphi, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      rcases p9823_3 (m.d 0 4) (by simp) with h9839 | h9839
                      · linarith only [h6874, h9839, hlam]
                      · linarith only [h8887, h9839, hlam]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8891, h8894, h8896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8891, h8894, h8896, h9361, h9651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9725_1, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8887, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8892, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8896, hlam, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h9461, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8889, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8894, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8896, hc23, hc34, hlam, hphi, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h9651, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8890, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8895, hlam, p9823_0]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h8890, h8896, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [h6874, h8890, h8891, h8894, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9823_1]
                    · have p9823_0 := h9823c.1
                      have p9823_1 := h9823c.2.1
                      have p9823_2 := h9823c.2.2.1
                      have p9823_3 := h9823c.2.2.2
                      linarith only [hlam, p9823_0]
                  · linarith only [h9461, h9822, hlam]
            · linarith only [h8892, h9817, hlam]
          · linarith only [h8887, h9816, hlam]
        · have p9725_0 := h9725c.1
          have p9725_1 := h9725c.2.1
          have p9725_2 := h9725c.2.2.1
          have p9725_3 := h9725c.2.2.2
          linarith only [hlam, p9725_0]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8894 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8895 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 2 3 4 (by decide) (by decide) with h8896 | h8896
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893 h8894 h8895 h8896
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893 h8894 h8895 h8896

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8894 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8895 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h6874, h8890, h8895, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8894 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 4 5 (by decide) (by decide) with h8895 | h8895
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893 h8894 h8895
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893 h8894 h8895

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8894 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h6874, h8889, h8894, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 3 4 (by decide) (by decide) with h8894 | h8894
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893 h8894
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893 h8894

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8893 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h8888, h8893, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 5 (by decide) (by decide) with h8893 | h8893
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892 h8893

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8892 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h8887, h8892, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 4 (by decide) (by decide) with h8892 | h8892
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891 h8892

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8891 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h8886, h8891, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 3 (by decide) (by decide) with h8891 | h8891
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891
  · exact r1l7_12_24_L_I_H_I_s10_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h8890 h8891

end R2N4
