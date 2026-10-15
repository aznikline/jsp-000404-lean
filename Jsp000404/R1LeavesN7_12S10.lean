import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s12_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h8381 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8382 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8383 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8384 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8385 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8386 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h8387 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h8388 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h8389 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h8390 | h8390
  · rcases m.htr 2 4 5 (by decide) (by decide) with h8391 | h8391
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8392 | h8392
      · linarith only [h8378, h8389, h8392, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases h1bigk with h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c | h8394c
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h0, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h6794, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h7647, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8170, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          rcases p8394_3 (m.d 0 1) (by simp) with h8400 | h8400
          · linarith only [h8400, hlam, p8394_0]
          · rcases p8394_3 (m.d 1 2) (by simp) with h8402 | h8402
            · rcases p8394_3 (m.d 1 3) (by simp) with h8403 | h8403
              · linarith only [h8383, h8403, hlam]
              · linarith only [h6794, h8403, hlam]
            · linarith only [h8402, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h6794, hc01, hc12, hlam, hphi, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h7647, h8379, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8170, hc01, hc12, hlam, hphi, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          rcases p8394_3 (m.d 0 1) (by simp) with h8411 | h8411
          · linarith only [h8411, hlam, p8394_0]
          · rcases p8394_3 (m.d 1 2) (by simp) with h8413 | h8413
            · rcases p8394_3 (m.d 1 3) (by simp) with h8414 | h8414
              · rcases p8394_3 (m.d 1 4) (by simp) with h8415 | h8415
                · linarith only [h8386, h8415, hlam]
                · linarith only [h7647, h8415, hlam]
              · linarith only [h8414, hlam, p8394_0]
            · linarith only [h0, h8413, hlam]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8383, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h7647, h8379, h8391, h8392, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8170, h8383, hc01, hc12, hlam, hphi, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          rcases p8394_3 (m.d 0 1) (by simp) with h8424 | h8424
          · linarith only [h8424, hlam, p8394_0]
          · rcases p8394_3 (m.d 1 2) (by simp) with h8426 | h8426
            · rcases p8394_3 (m.d 1 3) (by simp) with h8427 | h8427
              · rcases p8394_3 (m.d 1 4) (by simp) with h8428 | h8428
                · rcases p8394_3 (m.d 1 5) (by simp) with h8429 | h8429
                  · linarith only [h8388, h8429, hlam]
                  · linarith only [h8170, h8429, hlam]
                · linarith only [h8428, hlam, p8394_0]
              · linarith only [h6794, h8427, hlam]
            · linarith only [h0, h8426, hlam]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8384, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8386, hlam, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8170, hc01, hc14, hlam, hphi, p8394_1]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          rcases p8394_3 (m.d 0 1) (by simp) with h8439 | h8439
          · linarith only [h8439, hlam, p8394_0]
          · rcases p8394_3 (m.d 1 2) (by simp) with h8441 | h8441
            · rcases p8394_3 (m.d 1 3) (by simp) with h8442 | h8442
              · rcases p8394_3 (m.d 1 4) (by simp) with h8443 | h8443
                · rcases p8394_3 (m.d 1 5) (by simp) with h8444 | h8444
                  · rcases h2bigk with h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c | h8445c
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h0, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h0, h8389, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h0, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      rcases p8445_3 (m.d 0 2) (by simp) with h8450 | h8450
                      · rcases p8445_3 (m.d 1 2) (by simp) with h8451 | h8451
                        · rcases p8445_3 (m.d 2 3) (by simp) with h8452 | h8452
                          · linarith only [h8378, h8452, hlam]
                          · linarith only [h8390, h8452, hlam]
                        · linarith only [h8385, h8451, hlam]
                      · linarith only [h8450, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8378, h8389, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8389, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      rcases p8445_3 (m.d 0 2) (by simp) with h8461 | h8461
                      · linarith only [h0, h8461, hlam]
                      · linarith only [h8380, h8461, hlam]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8378, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8383, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8378, h8391, h8392, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h0, h8378, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8379, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8384, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8389, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h0, h8379, h8391, h8392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8380, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8385, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8390, hlam, p8445_0]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [h8391, hlam, p8445_1]
                    · have p8445_0 := h8445c.1
                      have p8445_1 := h8445c.2.1
                      have p8445_2 := h8445c.2.2.1
                      have p8445_3 := h8445c.2.2.2
                      linarith only [hlam, p8445_0]
                  · linarith only [h8444, hlam, p8394_0]
                · linarith only [h7647, h8443, hlam]
              · linarith only [h6794, h8442, hlam]
            · linarith only [h0, h8441, hlam]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8385, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8387, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [h8388, hlam, p8394_0]
        · have p8394_0 := h8394c.1
          have p8394_1 := h8394c.2.1
          have p8394_2 := h8394c.2.2.1
          have p8394_3 := h8394c.2.2.2
          linarith only [hlam, p8394_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8487 | h8487
      · linarith only [h0, h8378, h8389, h8391, h8487, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h0, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h6794, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h7647, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8170, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          rcases p8489_3 (m.d 0 1) (by simp) with h8495 | h8495
          · linarith only [h8495, hlam, p8489_0]
          · rcases p8489_3 (m.d 1 2) (by simp) with h8497 | h8497
            · rcases p8489_3 (m.d 1 3) (by simp) with h8498 | h8498
              · linarith only [h8383, h8498, hlam]
              · linarith only [h6794, h8498, hlam]
            · linarith only [h8497, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h6794, hc01, hc12, hlam, hphi, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h7647, h8382, h8389, h8391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8170, hc01, hc12, hlam, hphi, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          rcases p8489_3 (m.d 0 1) (by simp) with h8506 | h8506
          · linarith only [h8506, hlam, p8489_0]
          · rcases p8489_3 (m.d 1 2) (by simp) with h8508 | h8508
            · rcases p8489_3 (m.d 1 3) (by simp) with h8509 | h8509
              · rcases p8489_3 (m.d 1 4) (by simp) with h8510 | h8510
                · linarith only [h8386, h8510, hlam]
                · linarith only [h7647, h8510, hlam]
              · linarith only [h8509, hlam, p8489_0]
            · linarith only [h0, h8508, hlam]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8383, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h7647, h8382, h8389, h8391, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8170, h8383, hc01, hc12, hlam, hphi, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          rcases p8489_3 (m.d 0 1) (by simp) with h8519 | h8519
          · linarith only [h8519, hlam, p8489_0]
          · rcases p8489_3 (m.d 1 2) (by simp) with h8521 | h8521
            · rcases p8489_3 (m.d 1 3) (by simp) with h8522 | h8522
              · rcases p8489_3 (m.d 1 4) (by simp) with h8523 | h8523
                · rcases p8489_3 (m.d 1 5) (by simp) with h8524 | h8524
                  · linarith only [h8388, h8524, hlam]
                  · linarith only [h8170, h8524, hlam]
                · linarith only [h8523, hlam, p8489_0]
              · linarith only [h6794, h8522, hlam]
            · linarith only [h0, h8521, hlam]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8384, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8386, hlam, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8170, hc01, hc14, hlam, hphi, p8489_1]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          rcases p8489_3 (m.d 0 1) (by simp) with h8534 | h8534
          · linarith only [h8534, hlam, p8489_0]
          · rcases p8489_3 (m.d 1 2) (by simp) with h8536 | h8536
            · rcases p8489_3 (m.d 1 3) (by simp) with h8537 | h8537
              · rcases p8489_3 (m.d 1 4) (by simp) with h8538 | h8538
                · rcases p8489_3 (m.d 1 5) (by simp) with h8539 | h8539
                  · rcases h2bigk with h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h0, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h0, h8390, hc12, hlam, hphi, ht01, ht0b, ht5b, p8540_1, u5ehi3]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      rcases p8540_3 (m.d 0 2) (by simp) with h8544 | h8544
                      · rcases p8540_3 (m.d 1 2) (by simp) with h8545 | h8545
                        · rcases p8540_3 (m.d 2 3) (by simp) with h8546 | h8546
                          · linarith only [h8378, h8546, hlam]
                          · linarith only [h8389, h8546, hlam]
                        · linarith only [h8384, h8545, hlam]
                      · linarith only [h8544, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      rcases p8540_3 (m.d 0 2) (by simp) with h8551 | h8551
                      · rcases p8540_3 (m.d 1 2) (by simp) with h8552 | h8552
                        · rcases p8540_3 (m.d 2 3) (by simp) with h8553 | h8553
                          · linarith only [h8378, h8553, hlam]
                          · linarith only [h8390, h8553, hlam]
                        · linarith only [h8385, h8552, hlam]
                      · linarith only [h8551, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8378, h8390, hc12, hlam, hphi, ht01, ht0b, ht5b, p8540_1, u5ehi3]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8390, hc12, hlam, hphi, ht01, ht0b, ht5b, p8540_1, u5ehi3]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      rcases p8540_3 (m.d 0 2) (by simp) with h8561 | h8561
                      · linarith only [h0, h8561, hlam]
                      · linarith only [h8379, h8561, hlam]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      rcases p8540_3 (m.d 0 2) (by simp) with h8564 | h8564
                      · linarith only [h0, h8564, hlam]
                      · linarith only [h8380, h8564, hlam]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8378, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8383, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      rcases p8540_3 (m.d 0 2) (by simp) with h8570 | h8570
                      · rcases p8540_3 (m.d 1 2) (by simp) with h8571 | h8571
                        · rcases p8540_3 (m.d 2 3) (by simp) with h8572 | h8572
                          · rcases p8540_3 (m.d 2 4) (by simp) with h8573 | h8573
                            · linarith only [h8389, h8573, hlam]
                            · rcases p8540_3 (m.d 2 5) (by simp) with h8575 | h8575
                              · linarith only [h8390, h8575, hlam]
                              · linarith only [h8391, h8575, hlam]
                          · linarith only [h8389, h8572, hlam]
                        · linarith only [h8384, h8571, hlam]
                      · linarith only [h8379, h8570, hlam]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8378, h8390, hc02, hlam, hphi, ht0b, ht5b, p8540_1, u5ehi3]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8379, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8384, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8389, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8391, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8380, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8385, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [h8390, hlam, p8540_0]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      rcases p8540_3 (m.d 0 2) (by simp) with h8590 | h8590
                      · rcases p8540_3 (m.d 1 2) (by simp) with h8591 | h8591
                        · rcases p8540_3 (m.d 2 3) (by simp) with h8592 | h8592
                          · rcases p8540_3 (m.d 2 4) (by simp) with h8593 | h8593
                            · linarith only [h8391, h8593, hlam]
                            · rcases p8540_3 (m.d 2 5) (by simp) with h8595 | h8595
                              · rcases h4bigk with h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c | h8596c
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h7647, hlam, p8596_1]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8382, h8391, hlam, p8540_1, p8596_2]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8382, h8389, h8391, hlam, p8540_1, p8596_2]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8389, h8391, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8540_1, p8596_1]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8382, h8383, h8386, h8389, h8391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8540_1, p8596_1]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h7647, h8382, h8391, hlam, p8540_1, p8596_2]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h7647, h8382, h8389, h8391, hlam, p8540_1, p8596_2]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8389, h8391, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8540_1, p8596_1]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8379, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8384, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8382, h8391, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8540_1, p8596_1]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8391, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8381, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8386, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8389, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8487, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8382, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [h8388, hlam, p8596_0]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  rcases p8596_3 (m.d 0 4) (by simp) with h8619 | h8619
                                  · rcases p8596_3 (m.d 1 4) (by simp) with h8620 | h8620
                                    · rcases p8596_3 (m.d 2 4) (by simp) with h8621 | h8621
                                      · linarith only [h8621, hlam, p8596_0]
                                      · rcases p8596_3 (m.d 3 4) (by simp) with h8623 | h8623
                                        · linarith only [h8487, h8623, hlam]
                                        · rcases p8596_3 (m.d 4 5) (by simp) with h8625 | h8625
                                          · rcases h5bigk with h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c | h8626c
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8170, hlam, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p8540_1, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              rcases p8626_3 (m.d 0 5) (by simp) with h8630 | h8630
                                              · rcases p8626_3 (m.d 1 5) (by simp) with h8631 | h8631
                                                · rcases p8626_3 (m.d 2 5) (by simp) with h8632 | h8632
                                                  · linarith only [h8380, h8632, hlam]
                                                  · linarith only [h8390, h8632, hlam]
                                                · linarith only [h8387, h8631, hlam]
                                              · linarith only [h8630, hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8389, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p8596_1, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8380, h8389, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8540_1, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8385, h8389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8540_1, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              rcases p8626_3 (m.d 0 5) (by simp) with h8641 | h8641
                                              · linarith only [h8170, h8641, hlam]
                                              · linarith only [h8382, h8383, h8386, h8388, h8389, h8391, h8641, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8540_1, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8383, h8386, h8388, h8389, h8391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8540_1, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8380, hlam, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8385, hlam, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h0, h8380, hc12, hlam, hphi, ht01, ht0b, ht5b, p8626_1, u5ehi3]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8391, hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8383, h8387, hc12, hlam, hphi, ht01, ht0b, ht5b, p8626_1, u5ehi0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8387, hlam, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8390, hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8487, hlam, p8626_0]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8382, hlam, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h8388, hlam, p8626_1]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h0, h8378, h8381, h8382, hc12, hlam, hphi, ht01, ht0b, ht5b, p8626_1, u5ehi2]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [h0, h8378, h8381, h8382, hc12, hlam, hphi, ht01, ht0b, ht5b, p8626_1, u5ehi3]
                                            · have p8626_0 := h8626c.1
                                              have p8626_1 := h8626c.2.1
                                              have p8626_2 := h8626c.2.2.1
                                              have p8626_3 := h8626c.2.2.2
                                              linarith only [hlam, p8626_0]
                                          · linarith only [h8625, hlam, p8596_0]
                                    · linarith only [h8384, h8620, hlam]
                                  · linarith only [h8379, h8619, hlam]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  rcases p8596_3 (m.d 0 4) (by simp) with h8663 | h8663
                                  · rcases p8596_3 (m.d 1 4) (by simp) with h8664 | h8664
                                    · rcases p8596_3 (m.d 2 4) (by simp) with h8665 | h8665
                                      · linarith only [h8391, h8665, hlam]
                                      · linarith only [h8389, h8665, hlam]
                                    · linarith only [h8386, h8664, hlam]
                                  · linarith only [h8381, h8663, hlam]
                                · have p8596_0 := h8596c.1
                                  have p8596_1 := h8596c.2.1
                                  have p8596_2 := h8596c.2.2.1
                                  have p8596_3 := h8596c.2.2.2
                                  linarith only [hlam, p8596_0]
                              · linarith only [h8391, h8595, hlam]
                          · linarith only [h8389, h8592, hlam]
                        · linarith only [h8384, h8591, hlam]
                      · linarith only [h8379, h8590, hlam]
                    · have p8540_0 := h8540c.1
                      have p8540_1 := h8540c.2.1
                      have p8540_2 := h8540c.2.2.1
                      have p8540_3 := h8540c.2.2.2
                      linarith only [hlam, p8540_0]
                  · linarith only [h8539, hlam, p8489_0]
                · linarith only [h7647, h8538, hlam]
              · linarith only [h6794, h8537, hlam]
            · linarith only [h0, h8536, hlam]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8385, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8387, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [h8388, hlam, p8489_0]
        · have p8489_0 := h8489c.1
          have p8489_1 := h8489c.2.1
          have p8489_2 := h8489c.2.2.1
          have p8489_3 := h8489c.2.2.2
          linarith only [hlam, p8489_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h8684 | h8684
    · linarith only [h8383, h8387, h8389, h8390, h8684, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8686 | h8686
      · linarith only [h8383, h8387, h8389, h8390, h8684, h8686, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c | h8688c
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h0, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h6794, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h7647, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8170, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          rcases p8688_3 (m.d 0 1) (by simp) with h8694 | h8694
          · linarith only [h8694, hlam, p8688_0]
          · rcases p8688_3 (m.d 1 2) (by simp) with h8696 | h8696
            · rcases p8688_3 (m.d 1 3) (by simp) with h8697 | h8697
              · linarith only [h8383, h8697, hlam]
              · linarith only [h6794, h8697, hlam]
            · linarith only [h8696, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h6794, hc01, hc12, hlam, hphi, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h7647, hc01, hc12, hlam, hphi, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8170, hc01, hc12, hlam, hphi, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          rcases p8688_3 (m.d 0 1) (by simp) with h8705 | h8705
          · linarith only [h8705, hlam, p8688_0]
          · rcases p8688_3 (m.d 1 2) (by simp) with h8707 | h8707
            · rcases p8688_3 (m.d 1 3) (by simp) with h8708 | h8708
              · rcases p8688_3 (m.d 1 4) (by simp) with h8709 | h8709
                · linarith only [h8386, h8709, hlam]
                · linarith only [h7647, h8709, hlam]
              · linarith only [h8708, hlam, p8688_0]
            · linarith only [h0, h8707, hlam]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8383, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h7647, h8382, h8390, h8686, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8170, h8383, hc01, hc12, hlam, hphi, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          rcases p8688_3 (m.d 0 1) (by simp) with h8718 | h8718
          · linarith only [h8718, hlam, p8688_0]
          · rcases p8688_3 (m.d 1 2) (by simp) with h8720 | h8720
            · rcases p8688_3 (m.d 1 3) (by simp) with h8721 | h8721
              · rcases p8688_3 (m.d 1 4) (by simp) with h8722 | h8722
                · rcases p8688_3 (m.d 1 5) (by simp) with h8723 | h8723
                  · linarith only [h8388, h8723, hlam]
                  · linarith only [h8170, h8723, hlam]
                · linarith only [h8722, hlam, p8688_0]
              · linarith only [h6794, h8721, hlam]
            · linarith only [h0, h8720, hlam]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8384, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8386, hlam, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8170, h8382, h8389, h8390, h8686, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8688_1]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          rcases p8688_3 (m.d 0 1) (by simp) with h8733 | h8733
          · linarith only [h8733, hlam, p8688_0]
          · rcases p8688_3 (m.d 1 2) (by simp) with h8735 | h8735
            · rcases p8688_3 (m.d 1 3) (by simp) with h8736 | h8736
              · rcases p8688_3 (m.d 1 4) (by simp) with h8737 | h8737
                · rcases p8688_3 (m.d 1 5) (by simp) with h8738 | h8738
                  · rcases h2bigk with h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h0, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8742 | h8742
                      · rcases p8739_3 (m.d 1 2) (by simp) with h8743 | h8743
                        · rcases p8739_3 (m.d 2 3) (by simp) with h8744 | h8744
                          · linarith only [h8744, hlam, p8739_0]
                          · rcases p8739_3 (m.d 2 4) (by simp) with h8746 | h8746
                            · linarith only [h8379, h8746, hlam]
                            · rcases p8739_3 (m.d 2 5) (by simp) with h8748 | h8748
                              · linarith only [h8380, h8748, hlam]
                              · linarith only [h8390, h8748, hlam]
                        · linarith only [h8383, h8743, hlam]
                      · linarith only [h8742, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8753 | h8753
                      · rcases p8739_3 (m.d 1 2) (by simp) with h8754 | h8754
                        · rcases p8739_3 (m.d 2 3) (by simp) with h8755 | h8755
                          · linarith only [h8378, h8755, hlam]
                          · linarith only [h8389, h8755, hlam]
                        · linarith only [h8384, h8754, hlam]
                      · linarith only [h8753, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8760 | h8760
                      · rcases p8739_3 (m.d 1 2) (by simp) with h8761 | h8761
                        · rcases p8739_3 (m.d 2 3) (by simp) with h8762 | h8762
                          · linarith only [h8378, h8762, hlam]
                          · rcases p8739_3 (m.d 2 4) (by simp) with h8764 | h8764
                            · linarith only [h8379, h8764, hlam]
                            · rcases p8739_3 (m.d 2 5) (by simp) with h8766 | h8766
                              · linarith only [h8766, hlam, p8739_0]
                              · rcases h4bigk with h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h7647, hlam, p8768_1]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  rcases p8768_3 (m.d 0 4) (by simp) with h8771 | h8771
                                  · rcases p8768_3 (m.d 1 4) (by simp) with h8772 | h8772
                                    · rcases p8768_3 (m.d 2 4) (by simp) with h8773 | h8773
                                      · linarith only [h8379, h8773, hlam]
                                      · rcases p8768_3 (m.d 3 4) (by simp) with h8775 | h8775
                                        · linarith only [h8381, h8775, hlam]
                                        · rcases p8768_3 (m.d 4 5) (by simp) with h8777 | h8777
                                          · linarith only [h8382, h8777, hlam]
                                          · linarith only [h8684, h8777, hlam]
                                    · linarith only [h8384, h8772, hlam]
                                  · linarith only [h8379, h8771, hlam]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8382, h8389, h8390, h8686, hlam, p8768_2]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8389, h8390, h8686, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8768_1]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8382, h8383, h8386, h8389, h8390, h8686, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8768_1]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  rcases p8768_3 (m.d 0 4) (by simp) with h8786 | h8786
                                  · linarith only [h7647, h8786, hlam]
                                  · linarith only [h8379, h8786, hlam]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h7647, h8382, h8389, h8390, h8686, hlam, p8768_2]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8389, h8390, h8686, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8768_1]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8379, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8384, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8382, h8389, h8390, h8686, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8768_1]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8684, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8381, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8386, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8389, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8686, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8382, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [h8388, hlam, p8768_0]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  rcases p8768_3 (m.d 0 4) (by simp) with h8803 | h8803
                                  · rcases p8768_3 (m.d 1 4) (by simp) with h8804 | h8804
                                    · rcases p8768_3 (m.d 2 4) (by simp) with h8805 | h8805
                                      · linarith only [h8805, hlam, p8768_0]
                                      · rcases p8768_3 (m.d 3 4) (by simp) with h8807 | h8807
                                        · linarith only [h8686, h8807, hlam]
                                        · rcases p8768_3 (m.d 4 5) (by simp) with h8809 | h8809
                                          · rcases h5bigk with h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c | h8810c
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [hlam, p8810_0]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8170, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              rcases p8810_3 (m.d 0 5) (by simp) with h8813 | h8813
                                              · rcases p8810_3 (m.d 1 5) (by simp) with h8814 | h8814
                                                · rcases p8810_3 (m.d 2 5) (by simp) with h8815 | h8815
                                                  · linarith only [h8380, h8815, hlam]
                                                  · rcases p8810_3 (m.d 3 5) (by simp) with h8817 | h8817
                                                    · linarith only [h7647, h8382, h8383, h8386, h8686, h8817, hc12, hlam, hphi, ht01, ht0b, ht5b, p8810_1, u5ehi2]
                                                    · linarith only [h8390, h8817, hlam]
                                                · linarith only [h8385, h8814, hlam]
                                              · linarith only [h8380, h8813, hlam]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8389, h8390, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h7647, h8382, h8383, h8386, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8768_1, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8382, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8768_1, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [hlam, p8810_0]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              rcases p8810_3 (m.d 0 5) (by simp) with h8826 | h8826
                                              · linarith only [h8170, h8826, hlam]
                                              · linarith only [h8380, h8826, hlam]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8383, h8386, h8388, h8389, h8390, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8383, h8386, h8388, h8389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8768_1, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8380, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8385, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [hlam, p8810_0]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8390, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8684, hlam, p8810_0]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8382, h8389, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p8768_1, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8387, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8383, h8387, h8389, h8390, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [hlam, p8810_0]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8686, hlam, p8810_0]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8382, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8388, hlam, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h8389, h8390, hc34, hc45, hlam, hphi, p8810_1]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [h7647, h8382, h8383, h8386, hc12, hlam, hphi, ht01, ht0b, ht5b, p8810_1, u5ehi3]
                                            · have p8810_0 := h8810c.1
                                              have p8810_1 := h8810c.2.1
                                              have p8810_2 := h8810c.2.2.1
                                              have p8810_3 := h8810c.2.2.2
                                              linarith only [hlam, p8810_0]
                                          · linarith only [h8809, hlam, p8768_0]
                                    · linarith only [h8384, h8804, hlam]
                                  · linarith only [h8379, h8803, hlam]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  rcases p8768_3 (m.d 0 4) (by simp) with h8849 | h8849
                                  · rcases p8768_3 (m.d 1 4) (by simp) with h8850 | h8850
                                    · rcases p8768_3 (m.d 2 4) (by simp) with h8851 | h8851
                                      · linarith only [h8684, h8851, hlam]
                                      · linarith only [h8389, h8851, hlam]
                                    · linarith only [h8386, h8850, hlam]
                                  · linarith only [h8381, h8849, hlam]
                                · have p8768_0 := h8768c.1
                                  have p8768_1 := h8768c.2.1
                                  have p8768_2 := h8768c.2.2.1
                                  have p8768_3 := h8768c.2.2.2
                                  linarith only [hlam, p8768_0]
                        · linarith only [h8385, h8761, hlam]
                      · linarith only [h8760, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8378, h8389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8739_1]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8861 | h8861
                      · linarith only [h0, h8861, hlam]
                      · linarith only [h8378, h8861, hlam]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8864 | h8864
                      · linarith only [h0, h8864, hlam]
                      · linarith only [h8379, h8864, hlam]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8867 | h8867
                      · linarith only [h0, h8867, hlam]
                      · linarith only [h8380, h8867, hlam]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8378, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8383, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8383, h8387, h8390, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8739_1]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8390, hlam, p8739_1]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8379, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8384, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8389, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8684, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8380, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h8385, hlam, p8739_0]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [h0, h8380, h8389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8739_1]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      rcases p8739_3 (m.d 0 2) (by simp) with h8883 | h8883
                      · rcases p8739_3 (m.d 1 2) (by simp) with h8884 | h8884
                        · rcases p8739_3 (m.d 2 3) (by simp) with h8885 | h8885
                          · linarith only [h8390, h8885, hlam]
                          · linarith only [h8389, h8885, hlam]
                        · linarith only [h8384, h8884, hlam]
                      · linarith only [h8379, h8883, hlam]
                    · have p8739_0 := h8739c.1
                      have p8739_1 := h8739c.2.1
                      have p8739_2 := h8739c.2.2.1
                      have p8739_3 := h8739c.2.2.2
                      linarith only [hlam, p8739_0]
                  · linarith only [h8738, hlam, p8688_0]
                · linarith only [h7647, h8737, hlam]
              · linarith only [h6794, h8736, hlam]
            · linarith only [h0, h8735, hlam]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8385, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8387, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [h8388, hlam, p8688_0]
        · have p8688_0 := h8688c.1
          have p8688_1 := h8688c.2.1
          have p8688_2 := h8688c.2.2.1
          have p8688_3 := h8688c.2.2.2
          linarith only [hlam, p8688_0]

end R2N4
