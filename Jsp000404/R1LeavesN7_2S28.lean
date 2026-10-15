import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20421 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20422 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 3 4 5 (by decide) (by decide) with h20423 | h20423
  · rcases h0bigk with h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c | h20424c
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h0, hlam, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h14396, hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h16915, hlam, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h18815, hlam, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20430 | h20430
      · linarith only [h0, h20430, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20432 | h20432
        · rcases p20424_3 (m.d 0 3) (by simp) with h20433 | h20433
          · linarith only [h20408, h20433, hlam]
          · linarith only [h14396, h20433, hlam]
        · linarith only [h0, h20432, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h0, h20408, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20439 | h20439
      · linarith only [h0, h20439, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20441 | h20441
        · rcases p20424_3 (m.d 0 3) (by simp) with h20442 | h20442
          · linarith only [h20408, h20442, hlam]
          · linarith only [h20411, h20442, hlam]
        · linarith only [h20409, h20441, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20446 | h20446
      · linarith only [h0, h20446, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20448 | h20448
        · rcases p20424_3 (m.d 0 3) (by simp) with h20449 | h20449
          · linarith only [h20408, h20449, hlam]
          · linarith only [h20412, h20449, hlam]
        · linarith only [h20410, h20448, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20453 | h20453
      · linarith only [h14396, h20453, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20455 | h20455
        · rcases p20424_3 (m.d 0 3) (by simp) with h20456 | h20456
          · rcases p20424_3 (m.d 0 4) (by simp) with h20457 | h20457
            · linarith only [h20411, h20457, hlam]
            · linarith only [h16915, h20457, hlam]
          · linarith only [h14396, h20456, hlam]
        · linarith only [h0, h20455, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h20408, hlam, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20464 | h20464
      · linarith only [h14396, h20464, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20466 | h20466
        · rcases p20424_3 (m.d 0 3) (by simp) with h20467 | h20467
          · rcases p20424_3 (m.d 0 4) (by simp) with h20468 | h20468
            · linarith only [h20411, h20468, hlam]
            · rcases p20424_3 (m.d 0 5) (by simp) with h20470 | h20470
              · linarith only [h20412, h20470, hlam]
              · rcases h2bigk with h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c | h20472c
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h0, hlam, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20420, h20423, hc02, hc45, hlam, hphi, ht0b, ht5b, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  rcases p20472_3 (m.d 0 2) (by simp) with h20476 | h20476
                  · rcases p20472_3 (m.d 1 2) (by simp) with h20477 | h20477
                    · rcases p20472_3 (m.d 2 3) (by simp) with h20478 | h20478
                      · linarith only [h20408, h20478, hlam]
                      · linarith only [h20420, h20478, hlam]
                    · linarith only [h20415, h20477, hlam]
                  · linarith only [h20476, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  rcases p20472_3 (m.d 0 2) (by simp) with h20483 | h20483
                  · rcases p20472_3 (m.d 1 2) (by simp) with h20484 | h20484
                    · rcases p20472_3 (m.d 2 3) (by simp) with h20485 | h20485
                      · linarith only [h20408, h20485, hlam]
                      · linarith only [h20421, h20485, hlam]
                    · linarith only [h20416, h20484, hlam]
                  · linarith only [h20483, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20408, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  rcases p20472_3 (m.d 0 2) (by simp) with h20493 | h20493
                  · linarith only [h0, h20493, hlam]
                  · linarith only [h20409, h20493, hlam]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  rcases p20472_3 (m.d 0 2) (by simp) with h20496 | h20496
                  · linarith only [h0, h20496, hlam]
                  · linarith only [h20410, h20496, hlam]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20408, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20414, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h0, h20408, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  rcases p20472_3 (m.d 0 2) (by simp) with h20503 | h20503
                  · rcases p20472_3 (m.d 1 2) (by simp) with h20504 | h20504
                    · rcases p20472_3 (m.d 2 3) (by simp) with h20505 | h20505
                      · rcases p20472_3 (m.d 2 4) (by simp) with h20506 | h20506
                        · linarith only [h20420, h20506, hlam]
                        · linarith only [h20422, h20506, hlam]
                      · linarith only [h20421, h20505, hlam]
                    · linarith only [h20416, h20504, hlam]
                  · linarith only [h20410, h20503, hlam]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20409, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20415, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20420, hlam, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h14396, h20409, h20414, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20424_1, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20410, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20416, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20421, hlam, p20472_1]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [h20422, hlam, p20472_0]
                · have p20472_0 := h20472c.1
                  have p20472_1 := h20472c.2.1
                  have p20472_2 := h20472c.2.2.1
                  have p20472_3 := h20472c.2.2.2
                  linarith only [hlam, p20472_0]
          · linarith only [h20411, h20467, hlam]
        · linarith only [h20409, h20466, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20524 | h20524
      · linarith only [h14396, h20524, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20526 | h20526
        · rcases p20424_3 (m.d 0 3) (by simp) with h20527 | h20527
          · rcases p20424_3 (m.d 0 4) (by simp) with h20528 | h20528
            · linarith only [h20411, h20528, hlam]
            · linarith only [h20413, h20528, hlam]
          · linarith only [h20412, h20527, hlam]
        · linarith only [h20410, h20526, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20533 | h20533
      · linarith only [h16915, h20533, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20535 | h20535
        · rcases p20424_3 (m.d 0 3) (by simp) with h20536 | h20536
          · rcases p20424_3 (m.d 0 4) (by simp) with h20537 | h20537
            · rcases p20424_3 (m.d 0 5) (by simp) with h20538 | h20538
              · linarith only [h20413, h20538, hlam]
              · linarith only [h18815, h20538, hlam]
            · linarith only [h16915, h20537, hlam]
          · linarith only [h14396, h20536, hlam]
        · linarith only [h0, h20535, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h20409, hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h20411, hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20547 | h20547
      · linarith only [h16915, h20547, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20549 | h20549
        · rcases p20424_3 (m.d 0 3) (by simp) with h20550 | h20550
          · rcases p20424_3 (m.d 0 4) (by simp) with h20551 | h20551
            · rcases p20424_3 (m.d 0 5) (by simp) with h20552 | h20552
              · linarith only [h20413, h20552, hlam]
              · rcases h2bigk with h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c | h20554c
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h0, hlam, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h0, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  rcases p20554_3 (m.d 0 2) (by simp) with h20558 | h20558
                  · rcases p20554_3 (m.d 1 2) (by simp) with h20559 | h20559
                    · rcases p20554_3 (m.d 2 3) (by simp) with h20560 | h20560
                      · linarith only [h20408, h20560, hlam]
                      · linarith only [h20420, h20560, hlam]
                    · linarith only [h20415, h20559, hlam]
                  · linarith only [h20558, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  rcases p20554_3 (m.d 0 2) (by simp) with h20565 | h20565
                  · rcases p20554_3 (m.d 1 2) (by simp) with h20566 | h20566
                    · rcases p20554_3 (m.d 2 3) (by simp) with h20567 | h20567
                      · linarith only [h20408, h20567, hlam]
                      · linarith only [h20421, h20567, hlam]
                    · linarith only [h20416, h20566, hlam]
                  · linarith only [h20565, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20408, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  rcases p20554_3 (m.d 0 2) (by simp) with h20575 | h20575
                  · linarith only [h0, h20575, hlam]
                  · linarith only [h20409, h20575, hlam]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  rcases p20554_3 (m.d 0 2) (by simp) with h20578 | h20578
                  · linarith only [h0, h20578, hlam]
                  · linarith only [h20410, h20578, hlam]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20408, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20414, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20408, h20420, h20423, hc02, hc45, hlam, hphi, ht0b, ht5b, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  rcases p20554_3 (m.d 0 2) (by simp) with h20585 | h20585
                  · rcases p20554_3 (m.d 1 2) (by simp) with h20586 | h20586
                    · rcases p20554_3 (m.d 2 3) (by simp) with h20587 | h20587
                      · rcases p20554_3 (m.d 2 4) (by simp) with h20588 | h20588
                        · linarith only [h20420, h20588, hlam]
                        · linarith only [h20422, h20588, hlam]
                      · linarith only [h20421, h20587, hlam]
                    · linarith only [h20416, h20586, hlam]
                  · linarith only [h20410, h20585, hlam]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20409, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20415, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20420, hlam, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  rcases p20554_3 (m.d 0 2) (by simp) with h20598 | h20598
                  · rcases p20554_3 (m.d 1 2) (by simp) with h20599 | h20599
                    · rcases p20554_3 (m.d 2 3) (by simp) with h20600 | h20600
                      · rcases p20554_3 (m.d 2 4) (by simp) with h20601 | h20601
                        · rcases p20554_3 (m.d 2 5) (by simp) with h20602 | h20602
                          · linarith only [h20422, h20602, hlam]
                          · rcases h3bigk with h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c | h20604c
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h14396, hlam, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20420, hc03, hc25, hlam, hphi, ht0b, ht5b, p20554_1, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h14396, h20414, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              rcases p20604_3 (m.d 0 3) (by simp) with h20609 | h20609
                              · rcases p20604_3 (m.d 1 3) (by simp) with h20610 | h20610
                                · rcases p20604_3 (m.d 2 3) (by simp) with h20611 | h20611
                                  · linarith only [h20408, h20611, hlam]
                                  · linarith only [h20421, h20611, hlam]
                                · linarith only [h20418, h20610, hlam]
                              · linarith only [h20609, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20414, h20420, h20421, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20554_1, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20414, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              rcases p20604_3 (m.d 0 3) (by simp) with h20620 | h20620
                              · linarith only [h14396, h20620, hlam]
                              · linarith only [h20412, h20620, hlam]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20408, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20414, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h0, h20408, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20411, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20417, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20420, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20411, h20423, hc03, hc45, hlam, hphi, ht0b, ht5b, p20604_1]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20412, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20418, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20421, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [h20423, hlam, p20604_0]
                            · have p20604_0 := h20604c.1
                              have p20604_1 := h20604c.2.1
                              have p20604_2 := h20604c.2.2.1
                              have p20604_3 := h20604c.2.2.2
                              linarith only [hlam, p20604_0]
                        · linarith only [h20422, h20601, hlam]
                      · linarith only [h20421, h20600, hlam]
                    · linarith only [h20416, h20599, hlam]
                  · linarith only [h20410, h20598, hlam]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20410, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20416, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20421, hlam, p20554_1]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [h20422, hlam, p20554_0]
                · have p20554_0 := h20554c.1
                  have p20554_1 := h20554c.2.1
                  have p20554_2 := h20554c.2.2.1
                  have p20554_3 := h20554c.2.2.2
                  linarith only [hlam, p20554_0]
            · linarith only [h20413, h20551, hlam]
          · linarith only [h20412, h20550, hlam]
        · linarith only [h20410, h20549, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      rcases p20424_3 (m.d 0 1) (by simp) with h20650 | h20650
      · linarith only [h18815, h20650, hlam]
      · rcases p20424_3 (m.d 0 2) (by simp) with h20652 | h20652
        · rcases p20424_3 (m.d 0 3) (by simp) with h20653 | h20653
          · rcases p20424_3 (m.d 0 4) (by simp) with h20654 | h20654
            · rcases p20424_3 (m.d 0 5) (by simp) with h20655 | h20655
              · rcases h2bigk with h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c | h20656c
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h0, hlam, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h0, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  rcases p20656_3 (m.d 0 2) (by simp) with h20660 | h20660
                  · rcases p20656_3 (m.d 1 2) (by simp) with h20661 | h20661
                    · rcases p20656_3 (m.d 2 3) (by simp) with h20662 | h20662
                      · linarith only [h20408, h20662, hlam]
                      · linarith only [h20420, h20662, hlam]
                    · linarith only [h20415, h20661, hlam]
                  · linarith only [h20660, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  rcases p20656_3 (m.d 0 2) (by simp) with h20667 | h20667
                  · rcases p20656_3 (m.d 1 2) (by simp) with h20668 | h20668
                    · rcases p20656_3 (m.d 2 3) (by simp) with h20669 | h20669
                      · linarith only [h20408, h20669, hlam]
                      · linarith only [h20421, h20669, hlam]
                    · linarith only [h20416, h20668, hlam]
                  · linarith only [h20667, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20408, h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20420, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  rcases p20656_3 (m.d 0 2) (by simp) with h20677 | h20677
                  · linarith only [h0, h20677, hlam]
                  · linarith only [h20409, h20677, hlam]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  rcases p20656_3 (m.d 0 2) (by simp) with h20680 | h20680
                  · linarith only [h0, h20680, hlam]
                  · linarith only [h20410, h20680, hlam]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20408, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20414, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20408, h20420, h20423, hc02, hc45, hlam, hphi, ht0b, ht5b, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  rcases p20656_3 (m.d 0 2) (by simp) with h20687 | h20687
                  · rcases p20656_3 (m.d 1 2) (by simp) with h20688 | h20688
                    · rcases p20656_3 (m.d 2 3) (by simp) with h20689 | h20689
                      · rcases p20656_3 (m.d 2 4) (by simp) with h20690 | h20690
                        · linarith only [h20420, h20690, hlam]
                        · linarith only [h20422, h20690, hlam]
                      · linarith only [h20421, h20689, hlam]
                    · linarith only [h20416, h20688, hlam]
                  · linarith only [h20410, h20687, hlam]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20409, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20415, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20420, hlam, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  rcases p20656_3 (m.d 0 2) (by simp) with h20700 | h20700
                  · rcases p20656_3 (m.d 1 2) (by simp) with h20701 | h20701
                    · rcases p20656_3 (m.d 2 3) (by simp) with h20702 | h20702
                      · rcases p20656_3 (m.d 2 4) (by simp) with h20703 | h20703
                        · rcases p20656_3 (m.d 2 5) (by simp) with h20704 | h20704
                          · linarith only [h20422, h20704, hlam]
                          · rcases h3bigk with h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c | h20706c
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h14396, hlam, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h14396, h20414, h20420, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20656_1, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h14396, h20414, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              rcases p20706_3 (m.d 0 3) (by simp) with h20711 | h20711
                              · rcases p20706_3 (m.d 1 3) (by simp) with h20712 | h20712
                                · rcases p20706_3 (m.d 2 3) (by simp) with h20713 | h20713
                                  · linarith only [h20408, h20713, hlam]
                                  · linarith only [h20421, h20713, hlam]
                                · linarith only [h20418, h20712, hlam]
                              · linarith only [h20711, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20414, h20420, h20421, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20656_1, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20414, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              rcases p20706_3 (m.d 0 3) (by simp) with h20722 | h20722
                              · linarith only [h14396, h20722, hlam]
                              · linarith only [h20412, h20722, hlam]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20408, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20414, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20423, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h0, h20408, h20423, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20411, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20417, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20420, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20411, h20423, hc03, hc45, hlam, hphi, ht0b, ht5b, p20706_1]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20412, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20418, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20421, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [h20423, hlam, p20706_0]
                            · have p20706_0 := h20706c.1
                              have p20706_1 := h20706c.2.1
                              have p20706_2 := h20706c.2.2.1
                              have p20706_3 := h20706c.2.2.2
                              linarith only [hlam, p20706_0]
                        · linarith only [h20422, h20703, hlam]
                      · linarith only [h20421, h20702, hlam]
                    · linarith only [h20416, h20701, hlam]
                  · linarith only [h20410, h20700, hlam]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20410, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20416, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20421, hlam, p20656_1]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [h20422, hlam, p20656_0]
                · have p20656_0 := h20656c.1
                  have p20656_1 := h20656c.2.1
                  have p20656_2 := h20656c.2.2.1
                  have p20656_3 := h20656c.2.2.2
                  linarith only [hlam, p20656_0]
              · linarith only [h18815, h20655, hlam]
            · linarith only [h16915, h20654, hlam]
          · linarith only [h14396, h20653, hlam]
        · linarith only [h0, h20652, hlam]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h20410, hlam, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h20412, hlam, p20424_0]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [h20413, hlam, p20424_1]
    · have p20424_0 := h20424c.1
      have p20424_1 := h20424c.2.1
      have p20424_2 := h20424c.2.2.1
      have p20424_3 := h20424c.2.2.2
      linarith only [hlam, p20424_0]
  · rcases h0bigk with h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c | h20757c
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h0, hlam, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h14396, hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h16915, hlam, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h18815, hlam, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20763 | h20763
      · linarith only [h0, h20763, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20765 | h20765
        · rcases p20757_3 (m.d 0 3) (by simp) with h20766 | h20766
          · linarith only [h20408, h20766, hlam]
          · linarith only [h14396, h20766, hlam]
        · linarith only [h0, h20765, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h0, h20411, h20413, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h0, h20413, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20773 | h20773
      · linarith only [h0, h20773, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20775 | h20775
        · rcases p20757_3 (m.d 0 3) (by simp) with h20776 | h20776
          · linarith only [h20408, h20776, hlam]
          · linarith only [h20412, h20776, hlam]
        · linarith only [h20410, h20775, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20780 | h20780
      · linarith only [h14396, h20780, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20782 | h20782
        · rcases p20757_3 (m.d 0 3) (by simp) with h20783 | h20783
          · rcases p20757_3 (m.d 0 4) (by simp) with h20784 | h20784
            · linarith only [h20411, h20784, hlam]
            · linarith only [h16915, h20784, hlam]
          · linarith only [h14396, h20783, hlam]
        · linarith only [h0, h20782, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20408, hlam, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20409, h20422, h20423, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20792 | h20792
      · linarith only [h14396, h20792, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20794 | h20794
        · rcases p20757_3 (m.d 0 3) (by simp) with h20795 | h20795
          · rcases p20757_3 (m.d 0 4) (by simp) with h20796 | h20796
            · linarith only [h20411, h20796, hlam]
            · linarith only [h20413, h20796, hlam]
          · linarith only [h20412, h20795, hlam]
        · linarith only [h20410, h20794, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20801 | h20801
      · linarith only [h16915, h20801, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20803 | h20803
        · rcases p20757_3 (m.d 0 3) (by simp) with h20804 | h20804
          · rcases p20757_3 (m.d 0 4) (by simp) with h20805 | h20805
            · rcases p20757_3 (m.d 0 5) (by simp) with h20806 | h20806
              · linarith only [h20413, h20806, hlam]
              · linarith only [h18815, h20806, hlam]
            · linarith only [h16915, h20805, hlam]
          · linarith only [h14396, h20804, hlam]
        · linarith only [h0, h20803, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20409, hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20411, hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20815 | h20815
      · linarith only [h16915, h20815, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20817 | h20817
        · rcases p20757_3 (m.d 0 3) (by simp) with h20818 | h20818
          · rcases p20757_3 (m.d 0 4) (by simp) with h20819 | h20819
            · rcases p20757_3 (m.d 0 5) (by simp) with h20820 | h20820
              · linarith only [h20413, h20820, hlam]
              · rcases h2bigk with h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c | h20822c
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h0, hlam, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h0, h20420, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h0, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  rcases p20822_3 (m.d 0 2) (by simp) with h20827 | h20827
                  · rcases p20822_3 (m.d 1 2) (by simp) with h20828 | h20828
                    · rcases p20822_3 (m.d 2 3) (by simp) with h20829 | h20829
                      · linarith only [h20408, h20829, hlam]
                      · linarith only [h20421, h20829, hlam]
                    · linarith only [h20416, h20828, hlam]
                  · linarith only [h20827, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20408, h20420, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20420, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  rcases p20822_3 (m.d 0 2) (by simp) with h20838 | h20838
                  · linarith only [h0, h20838, hlam]
                  · linarith only [h20410, h20838, hlam]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20408, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20414, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20422, h20423, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h0, h20408, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20409, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20415, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20420, hlam, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h0, h20409, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20410, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20416, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20421, hlam, p20822_1]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [h20422, hlam, p20822_0]
                · have p20822_0 := h20822c.1
                  have p20822_1 := h20822c.2.1
                  have p20822_2 := h20822c.2.2.1
                  have p20822_3 := h20822c.2.2.2
                  linarith only [hlam, p20822_0]
            · linarith only [h20413, h20819, hlam]
          · linarith only [h20412, h20818, hlam]
        · linarith only [h20410, h20817, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      rcases p20757_3 (m.d 0 1) (by simp) with h20859 | h20859
      · linarith only [h18815, h20859, hlam]
      · rcases p20757_3 (m.d 0 2) (by simp) with h20861 | h20861
        · rcases p20757_3 (m.d 0 3) (by simp) with h20862 | h20862
          · rcases p20757_3 (m.d 0 4) (by simp) with h20863 | h20863
            · rcases p20757_3 (m.d 0 5) (by simp) with h20864 | h20864
              · rcases h2bigk with h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c | h20865c
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h0, hlam, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h0, h20420, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h0, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  rcases p20865_3 (m.d 0 2) (by simp) with h20870 | h20870
                  · rcases p20865_3 (m.d 1 2) (by simp) with h20871 | h20871
                    · rcases p20865_3 (m.d 2 3) (by simp) with h20872 | h20872
                      · linarith only [h20408, h20872, hlam]
                      · linarith only [h20421, h20872, hlam]
                    · linarith only [h20416, h20871, hlam]
                  · linarith only [h20870, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20408, h20420, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20420, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  rcases p20865_3 (m.d 0 2) (by simp) with h20881 | h20881
                  · linarith only [h0, h20881, hlam]
                  · linarith only [h20410, h20881, hlam]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20408, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20414, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20422, h20423, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20408, h20422, h20423, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20409, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20415, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20420, hlam, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h0, h20409, h20422, h20423, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20410, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20416, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20421, hlam, p20865_1]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [h20422, hlam, p20865_0]
                · have p20865_0 := h20865c.1
                  have p20865_1 := h20865c.2.1
                  have p20865_2 := h20865c.2.2.1
                  have p20865_3 := h20865c.2.2.2
                  linarith only [hlam, p20865_0]
              · linarith only [h18815, h20864, hlam]
            · linarith only [h16915, h20863, hlam]
          · linarith only [h14396, h20862, hlam]
        · linarith only [h0, h20861, hlam]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20410, hlam, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20412, hlam, p20757_0]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [h20413, hlam, p20757_1]
    · have p20757_0 := h20757c.1
      have p20757_1 := h20757c.2.1
      have p20757_2 := h20757c.2.2.1
      have p20757_3 := h20757c.2.2.2
      linarith only [hlam, p20757_0]

end R2N4
