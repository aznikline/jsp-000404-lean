import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
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
    (h20420 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h21506 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h21507 | h21507
  · rcases m.htr 3 4 5 (by decide) (by decide) with h21508 | h21508
    · rcases h0bigk with h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c | h21509c
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h0, hlam, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h14396, hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h16915, hlam, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h18815, hlam, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21515 | h21515
        · linarith only [h0, h21515, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21517 | h21517
          · rcases p21509_3 (m.d 0 3) (by simp) with h21518 | h21518
            · linarith only [h20408, h21518, hlam]
            · linarith only [h14396, h21518, hlam]
          · linarith only [h0, h21517, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h0, h20411, h20420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h0, h20411, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21525 | h21525
        · linarith only [h0, h21525, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21527 | h21527
          · rcases p21509_3 (m.d 0 3) (by simp) with h21528 | h21528
            · linarith only [h20408, h21528, hlam]
            · linarith only [h20412, h21528, hlam]
          · linarith only [h20410, h21527, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21532 | h21532
        · linarith only [h14396, h21532, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21534 | h21534
          · rcases p21509_3 (m.d 0 3) (by simp) with h21535 | h21535
            · rcases p21509_3 (m.d 0 4) (by simp) with h21536 | h21536
              · linarith only [h20411, h21536, hlam]
              · linarith only [h16915, h21536, hlam]
            · linarith only [h14396, h21535, hlam]
          · linarith only [h0, h21534, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20408, hlam, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20411, h20420, h21506, h21508, hc03, hc45, hlam, hphi, ht0b, ht5b, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21544 | h21544
        · linarith only [h14396, h21544, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21546 | h21546
          · rcases p21509_3 (m.d 0 3) (by simp) with h21547 | h21547
            · rcases p21509_3 (m.d 0 4) (by simp) with h21548 | h21548
              · linarith only [h20411, h21548, hlam]
              · linarith only [h20413, h21548, hlam]
            · linarith only [h20412, h21547, hlam]
          · linarith only [h20410, h21546, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21553 | h21553
        · linarith only [h16915, h21553, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21555 | h21555
          · rcases p21509_3 (m.d 0 3) (by simp) with h21556 | h21556
            · rcases p21509_3 (m.d 0 4) (by simp) with h21557 | h21557
              · rcases p21509_3 (m.d 0 5) (by simp) with h21558 | h21558
                · linarith only [h20413, h21558, hlam]
                · linarith only [h18815, h21558, hlam]
              · linarith only [h16915, h21557, hlam]
            · linarith only [h14396, h21556, hlam]
          · linarith only [h0, h21555, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20409, hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20411, hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21567 | h21567
        · linarith only [h16915, h21567, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21569 | h21569
          · rcases p21509_3 (m.d 0 3) (by simp) with h21570 | h21570
            · rcases p21509_3 (m.d 0 4) (by simp) with h21571 | h21571
              · rcases p21509_3 (m.d 0 5) (by simp) with h21572 | h21572
                · linarith only [h20413, h21572, hlam]
                · rcases h2bigk with h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c | h21574c
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h0, hlam, p21574_1]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21577 | h21577
                    · rcases p21574_3 (m.d 1 2) (by simp) with h21578 | h21578
                      · rcases p21574_3 (m.d 2 3) (by simp) with h21579 | h21579
                        · linarith only [h21579, hlam, p21574_0]
                        · rcases p21574_3 (m.d 2 4) (by simp) with h21581 | h21581
                          · linarith only [h20409, h21581, hlam]
                          · linarith only [h20420, h21581, hlam]
                      · linarith only [h20414, h21578, hlam]
                    · linarith only [h21577, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21586 | h21586
                    · rcases p21574_3 (m.d 1 2) (by simp) with h21587 | h21587
                      · rcases p21574_3 (m.d 2 3) (by simp) with h21588 | h21588
                        · linarith only [h20408, h21588, hlam]
                        · rcases p21574_3 (m.d 2 4) (by simp) with h21590 | h21590
                          · linarith only [h21590, hlam, p21574_0]
                          · rcases p21574_3 (m.d 2 5) (by simp) with h21592 | h21592
                            · linarith only [h20410, h21592, hlam]
                            · rcases h3bigk with h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c | h21594c
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h14396, hlam, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h14396, h20414, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h14396, h20414, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                rcases p21594_3 (m.d 0 3) (by simp) with h21599 | h21599
                                · rcases p21594_3 (m.d 1 3) (by simp) with h21600 | h21600
                                  · rcases p21594_3 (m.d 2 3) (by simp) with h21601 | h21601
                                    · linarith only [h20408, h21601, hlam]
                                    · linarith only [h21506, h21601, hlam]
                                  · linarith only [h20418, h21600, hlam]
                                · linarith only [h21599, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20414, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20414, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                rcases p21594_3 (m.d 0 3) (by simp) with h21610 | h21610
                                · linarith only [h14396, h21610, hlam]
                                · linarith only [h20412, h21610, hlam]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20408, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20414, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20420, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20420, h21508, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20411, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20417, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [hc23, hc34, hlam, hphi, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20411, h21508, hc03, hc45, hlam, hphi, ht0b, ht5b, p21594_1]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20412, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h20418, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h21506, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [h21508, hlam, p21594_0]
                              · have p21594_0 := h21594c.1
                                have p21594_1 := h21594c.2.1
                                have p21594_2 := h21594c.2.2.1
                                have p21594_3 := h21594c.2.2.2
                                linarith only [hlam, p21594_0]
                      · linarith only [h20415, h21587, hlam]
                    · linarith only [h21586, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21630 | h21630
                    · rcases p21574_3 (m.d 1 2) (by simp) with h21631 | h21631
                      · rcases p21574_3 (m.d 2 3) (by simp) with h21632 | h21632
                        · linarith only [h20408, h21632, hlam]
                        · linarith only [h21506, h21632, hlam]
                      · linarith only [h20416, h21631, hlam]
                    · linarith only [h21630, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20408, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21574_1]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21639 | h21639
                    · linarith only [h0, h21639, hlam]
                    · linarith only [h20408, h21639, hlam]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21642 | h21642
                    · linarith only [h0, h21642, hlam]
                    · linarith only [h20409, h21642, hlam]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21645 | h21645
                    · linarith only [h0, h21645, hlam]
                    · linarith only [h20410, h21645, hlam]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20408, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20414, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20420, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h14396, h20411, h20414, h20420, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p21574_1]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20409, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20415, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h14396, h20411, h20414, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21574_1]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    rcases p21574_3 (m.d 0 2) (by simp) with h21657 | h21657
                    · rcases p21574_3 (m.d 1 2) (by simp) with h21658 | h21658
                      · rcases p21574_3 (m.d 2 3) (by simp) with h21659 | h21659
                        · linarith only [h20420, h21659, hlam]
                        · linarith only [h21506, h21659, hlam]
                      · linarith only [h20416, h21658, hlam]
                    · linarith only [h20410, h21657, hlam]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20410, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h20416, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h21506, hlam, p21574_1]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [h21507, hlam, p21574_0]
                  · have p21574_0 := h21574c.1
                    have p21574_1 := h21574c.2.1
                    have p21574_2 := h21574c.2.2.1
                    have p21574_3 := h21574c.2.2.2
                    linarith only [hlam, p21574_0]
              · linarith only [h20413, h21571, hlam]
            · linarith only [h20412, h21570, hlam]
          · linarith only [h20410, h21569, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        rcases p21509_3 (m.d 0 1) (by simp) with h21672 | h21672
        · linarith only [h18815, h21672, hlam]
        · rcases p21509_3 (m.d 0 2) (by simp) with h21674 | h21674
          · rcases p21509_3 (m.d 0 3) (by simp) with h21675 | h21675
            · rcases p21509_3 (m.d 0 4) (by simp) with h21676 | h21676
              · rcases p21509_3 (m.d 0 5) (by simp) with h21677 | h21677
                · rcases h2bigk with h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c | h21678c
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h0, hlam, p21678_1]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21681 | h21681
                    · rcases p21678_3 (m.d 1 2) (by simp) with h21682 | h21682
                      · rcases p21678_3 (m.d 2 3) (by simp) with h21683 | h21683
                        · linarith only [h21683, hlam, p21678_0]
                        · rcases p21678_3 (m.d 2 4) (by simp) with h21685 | h21685
                          · linarith only [h20409, h21685, hlam]
                          · linarith only [h20420, h21685, hlam]
                      · linarith only [h20414, h21682, hlam]
                    · linarith only [h21681, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21690 | h21690
                    · rcases p21678_3 (m.d 1 2) (by simp) with h21691 | h21691
                      · rcases p21678_3 (m.d 2 3) (by simp) with h21692 | h21692
                        · linarith only [h20408, h21692, hlam]
                        · rcases p21678_3 (m.d 2 4) (by simp) with h21694 | h21694
                          · linarith only [h21694, hlam, p21678_0]
                          · rcases p21678_3 (m.d 2 5) (by simp) with h21696 | h21696
                            · linarith only [h20410, h21696, hlam]
                            · rcases h3bigk with h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c | h21698c
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h14396, hlam, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h14396, h20414, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h14396, h20414, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                rcases p21698_3 (m.d 0 3) (by simp) with h21703 | h21703
                                · rcases p21698_3 (m.d 1 3) (by simp) with h21704 | h21704
                                  · rcases p21698_3 (m.d 2 3) (by simp) with h21705 | h21705
                                    · linarith only [h20408, h21705, hlam]
                                    · linarith only [h21506, h21705, hlam]
                                  · linarith only [h20418, h21704, hlam]
                                · linarith only [h21703, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20414, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20414, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                rcases p21698_3 (m.d 0 3) (by simp) with h21714 | h21714
                                · linarith only [h14396, h21714, hlam]
                                · linarith only [h20412, h21714, hlam]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20408, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20414, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20420, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20420, h21508, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20411, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20417, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [hc23, hc34, hlam, hphi, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20411, h21508, hc03, hc45, hlam, hphi, ht0b, ht5b, p21698_1]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20412, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h20418, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h21506, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [h21508, hlam, p21698_0]
                              · have p21698_0 := h21698c.1
                                have p21698_1 := h21698c.2.1
                                have p21698_2 := h21698c.2.2.1
                                have p21698_3 := h21698c.2.2.2
                                linarith only [hlam, p21698_0]
                      · linarith only [h20415, h21691, hlam]
                    · linarith only [h21690, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21734 | h21734
                    · rcases p21678_3 (m.d 1 2) (by simp) with h21735 | h21735
                      · rcases p21678_3 (m.d 2 3) (by simp) with h21736 | h21736
                        · linarith only [h20408, h21736, hlam]
                        · linarith only [h21506, h21736, hlam]
                      · linarith only [h20416, h21735, hlam]
                    · linarith only [h21734, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20408, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21678_1]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21743 | h21743
                    · linarith only [h0, h21743, hlam]
                    · linarith only [h20408, h21743, hlam]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21746 | h21746
                    · linarith only [h0, h21746, hlam]
                    · linarith only [h20409, h21746, hlam]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21749 | h21749
                    · linarith only [h0, h21749, hlam]
                    · linarith only [h20410, h21749, hlam]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20408, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20414, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20420, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h14396, h20411, h20414, h20420, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p21678_1]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20409, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20415, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h14396, h20411, h20414, h20420, h21506, h21508, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21678_1]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    rcases p21678_3 (m.d 0 2) (by simp) with h21761 | h21761
                    · rcases p21678_3 (m.d 1 2) (by simp) with h21762 | h21762
                      · rcases p21678_3 (m.d 2 3) (by simp) with h21763 | h21763
                        · linarith only [h20420, h21763, hlam]
                        · linarith only [h21506, h21763, hlam]
                      · linarith only [h20416, h21762, hlam]
                    · linarith only [h20410, h21761, hlam]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20410, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h20416, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h21506, hlam, p21678_1]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [h21507, hlam, p21678_0]
                  · have p21678_0 := h21678c.1
                    have p21678_1 := h21678c.2.1
                    have p21678_2 := h21678c.2.2.1
                    have p21678_3 := h21678c.2.2.2
                    linarith only [hlam, p21678_0]
                · linarith only [h18815, h21677, hlam]
              · linarith only [h16915, h21676, hlam]
            · linarith only [h14396, h21675, hlam]
          · linarith only [h0, h21674, hlam]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20410, hlam, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20412, hlam, p21509_0]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [h20413, hlam, p21509_1]
      · have p21509_0 := h21509c.1
        have p21509_1 := h21509c.2.1
        have p21509_2 := h21509c.2.2.1
        have p21509_3 := h21509c.2.2.2
        linarith only [hlam, p21509_0]
    · linarith only [h16915, h20413, h20414, h20417, h20420, h21506, h21508, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
  · linarith only [h20420, h21506, h21507, hlam]

end R2N4
