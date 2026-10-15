import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x1_x1_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h13831 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14484 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14485 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h14486 | h14486
  · rcases m.htr 1 2 3 (by decide) (by decide) with h14487 | h14487
    · rcases m.htr 1 2 4 (by decide) (by decide) with h14488 | h14488
      · rcases m.htr 1 3 4 (by decide) (by decide) with h14489 | h14489
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14490 | h14490
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14491 | h14491
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14492 | h14492
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14493 | h14493
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14494 | h14494
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14495 | h14495
                    · rcases h3bigk with h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c | h14496c
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h7360, hlam, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h11548, hlam, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h11548, h14487, h14495, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        rcases p14496_3 (m.d 0 3) (by simp) with h14501 | h14501
                        · rcases p14496_3 (m.d 1 3) (by simp) with h14502 | h14502
                          · rcases p14496_3 (m.d 2 3) (by simp) with h14503 | h14503
                            · rcases p14496_3 (m.d 3 4) (by simp) with h14504 | h14504
                              · linarith only [h14484, h14504, hlam]
                              · linarith only [h14495, h14504, hlam]
                            · linarith only [h14493, h14503, hlam]
                          · linarith only [h14490, h14502, hlam]
                        · linarith only [h14501, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14484, h14487, h14495, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h0, h13831, h14487, h14492, hc01, hc12, hlam, hphi, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        rcases p14496_3 (m.d 0 3) (by simp) with h14513 | h14513
                        · linarith only [h14513, h7360, hlam]
                        · linarith only [h14484, h14513, hlam]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        rcases p14496_3 (m.d 0 3) (by simp) with h14516 | h14516
                        · linarith only [h14516, h7360, hlam]
                        · linarith only [h14485, h14516, hlam]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14484, h14495, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14487, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14487, h14495, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        rcases p14496_3 (m.d 0 3) (by simp) with h14523 | h14523
                        · linarith only [h11548, h14523, hlam]
                        · linarith only [h14485, h14523, hlam]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14484, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14489, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14492, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h11548, h14484, h14487, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p14496_1]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14485, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14490, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14493, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [h14495, hlam, p14496_0]
                      · have p14496_0 := h14496c.1
                        have p14496_1 := h14496c.2.1
                        have p14496_2 := h14496c.2.2.1
                        have p14496_3 := h14496c.2.2.2
                        linarith only [hlam, p14496_0]
                    · rcases h3bigk with h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c | h14536c
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h7360, hlam, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h11548, hlam, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        rcases p14536_3 (m.d 0 3) (by simp) with h14540 | h14540
                        · rcases p14536_3 (m.d 1 3) (by simp) with h14541 | h14541
                          · rcases p14536_3 (m.d 2 3) (by simp) with h14542 | h14542
                            · rcases p14536_3 (m.d 3 4) (by simp) with h14543 | h14543
                              · linarith only [h14543, hlam, p14536_0]
                              · rcases p14536_3 (m.d 3 5) (by simp) with h14545 | h14545
                                · linarith only [h14485, h14545, hlam]
                                · linarith only [h14495, h14545, hlam]
                            · linarith only [h14492, h14542, hlam]
                          · linarith only [h14489, h14541, hlam]
                        · linarith only [h14540, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        rcases p14536_3 (m.d 0 3) (by simp) with h14551 | h14551
                        · rcases p14536_3 (m.d 1 3) (by simp) with h14552 | h14552
                          · rcases p14536_3 (m.d 2 3) (by simp) with h14553 | h14553
                            · rcases p14536_3 (m.d 3 4) (by simp) with h14554 | h14554
                              · linarith only [h14484, h14554, hlam]
                              · rcases p14536_3 (m.d 3 5) (by simp) with h14556 | h14556
                                · linarith only [h14556, hlam, p14536_0]
                                · rcases h4bigk with h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c | h14558c
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h8811, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h13831, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h11548, h14484, h14487, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h11548, h14484, h14487, h14495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h8811, hc01, hc14, hlam, hphi, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h13831, h14486, h14488, h14495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    rcases p14558_3 (m.d 0 4) (by simp) with h14567 | h14567
                                    · linarith only [h14567, h8811, hlam]
                                    · linarith only [h14484, h14567, hlam]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14487, h14489, h14495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14486, h14495, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14488, hlam, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14487, h14492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14487, h14492, h14495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14484, hlam, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14489, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14492, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14495, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14486, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14491, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14494, hlam, p14558_0]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [h14486, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p14558_1]
                                  · have p14558_0 := h14558c.1
                                    have p14558_1 := h14558c.2.1
                                    have p14558_2 := h14558c.2.2.1
                                    have p14558_3 := h14558c.2.2.2
                                    linarith only [hlam, p14558_0]
                            · linarith only [h14493, h14553, hlam]
                          · linarith only [h14490, h14552, hlam]
                        · linarith only [h14551, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14484, h14486, h14487, h14495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h0, h11548, h14487, hc01, hc12, hlam, hphi, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        rcases p14536_3 (m.d 0 3) (by simp) with h14592 | h14592
                        · linarith only [h14592, h7360, hlam]
                        · linarith only [h14484, h14592, hlam]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        rcases p14536_3 (m.d 0 3) (by simp) with h14595 | h14595
                        · linarith only [h14595, h7360, hlam]
                        · linarith only [h14485, h14595, hlam]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14484, h14486, h14487, h14495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14487, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        rcases p14536_3 (m.d 0 3) (by simp) with h14601 | h14601
                        · linarith only [h11548, h14601, hlam]
                        · linarith only [h14484, h14601, hlam]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        rcases p14536_3 (m.d 0 3) (by simp) with h14604 | h14604
                        · linarith only [h11548, h14604, hlam]
                        · linarith only [h14485, h14604, hlam]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14484, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14489, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14492, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14495, hlam, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14485, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14490, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h14493, hlam, p14536_0]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [h11548, h14485, h14487, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14536_1]
                      · have p14536_0 := h14536c.1
                        have p14536_1 := h14536c.2.1
                        have p14536_2 := h14536c.2.2.1
                        have p14536_3 := h14536c.2.2.2
                        linarith only [hlam, p14536_0]
                  · linarith only [h13831, h14486, h14494, hlam]
                · linarith only [h11548, h14485, h14493, hlam]
              · linarith only [h11548, h14484, h14492, hlam]
            · linarith only [h13831, h14486, h14491, h8811, hc01, hc24, hlam, hphi, ht12]
          · linarith only [h11548, h14485, h14487, h14490, hlam]
        · linarith only [h11548, h14484, h14487, h14489, hlam]
      · linarith only [h0, h11548, h14487, h14488, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h14624 | h14624
      · linarith only [h0, h13831, h14487, h14624, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h14626 | h14626
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14627 | h14627
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14628 | h14628
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14629 | h14629
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14630 | h14630
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14631 | h14631
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14632 | h14632
                    · rcases h3bigk with h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c | h14633c
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h7360, hlam, p14633_1]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h11548, hlam, p14633_1]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14637 | h14637
                        · rcases p14633_3 (m.d 1 3) (by simp) with h14638 | h14638
                          · rcases p14633_3 (m.d 2 3) (by simp) with h14639 | h14639
                            · rcases p14633_3 (m.d 3 4) (by simp) with h14640 | h14640
                              · linarith only [h14640, hlam, p14633_0]
                              · rcases p14633_3 (m.d 3 5) (by simp) with h14642 | h14642
                                · linarith only [h14485, h14642, hlam]
                                · rcases h4bigk with h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c | h14644c
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h8811, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h13831, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14632, hc04, hc45, hlam, hphi, ht0b, ht5b, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    rcases p14644_3 (m.d 0 4) (by simp) with h14649 | h14649
                                    · rcases p14644_3 (m.d 1 4) (by simp) with h14650 | h14650
                                      · rcases p14644_3 (m.d 2 4) (by simp) with h14651 | h14651
                                        · rcases p14644_3 (m.d 3 4) (by simp) with h14652 | h14652
                                          · linarith only [h14484, h14652, hlam]
                                          · linarith only [h14632, h14652, hlam]
                                        · linarith only [h14631, h14651, hlam]
                                      · linarith only [h14628, h14650, hlam]
                                    · linarith only [h14649, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h8811, hc01, hc14, hlam, hphi, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14624, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14624, h14629, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    rcases p14644_3 (m.d 0 4) (by simp) with h14662 | h14662
                                    · linarith only [h14662, h8811, hlam]
                                    · linarith only [h14486, h14662, hlam]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14484, h14629, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14629, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    rcases p14644_3 (m.d 0 4) (by simp) with h14669 | h14669
                                    · linarith only [h13831, h14669, hlam]
                                    · linarith only [h14486, h14669, hlam]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14484, hlam, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14626, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14629, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14487, h7360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14633_1, p14644_1]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14486, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14628, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14631, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [h14632, hlam, p14644_0]
                                  · have p14644_0 := h14644c.1
                                    have p14644_1 := h14644c.2.1
                                    have p14644_2 := h14644c.2.2.1
                                    have p14644_3 := h14644c.2.2.2
                                    linarith only [hlam, p14644_0]
                            · linarith only [h14629, h14639, hlam]
                          · linarith only [h14626, h14638, hlam]
                        · linarith only [h14637, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14685 | h14685
                        · rcases p14633_3 (m.d 1 3) (by simp) with h14686 | h14686
                          · rcases p14633_3 (m.d 2 3) (by simp) with h14687 | h14687
                            · rcases p14633_3 (m.d 3 4) (by simp) with h14688 | h14688
                              · linarith only [h14484, h14688, hlam]
                              · linarith only [h14632, h14688, hlam]
                            · linarith only [h14630, h14687, hlam]
                          · linarith only [h14627, h14686, hlam]
                        · linarith only [h14685, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14484, h14487, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14633_1]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14487, hlam, p14633_1]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14697 | h14697
                        · linarith only [h14697, h7360, hlam]
                        · linarith only [h14484, h14697, hlam]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14700 | h14700
                        · linarith only [h14700, h7360, hlam]
                        · linarith only [h14485, h14700, hlam]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14484, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14633_1]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p14633_1]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14706 | h14706
                        · linarith only [h11548, h14706, hlam]
                        · linarith only [h14484, h14706, hlam]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14709 | h14709
                        · linarith only [h11548, h14709, hlam]
                        · linarith only [h14485, h14709, hlam]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14484, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14626, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14629, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        rcases p14633_3 (m.d 0 3) (by simp) with h14716 | h14716
                        · rcases p14633_3 (m.d 1 3) (by simp) with h14717 | h14717
                          · rcases p14633_3 (m.d 2 3) (by simp) with h14718 | h14718
                            · rcases p14633_3 (m.d 3 4) (by simp) with h14719 | h14719
                              · rcases p14633_3 (m.d 3 5) (by simp) with h14720 | h14720
                                · linarith only [h14632, h14720, hlam]
                                · rcases h4bigk with h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c | h14722c
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h8811, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h13831, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14632, hc04, hc45, hlam, hphi, ht0b, ht5b, p14633_1, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    rcases p14722_3 (m.d 0 4) (by simp) with h14727 | h14727
                                    · rcases p14722_3 (m.d 1 4) (by simp) with h14728 | h14728
                                      · rcases p14722_3 (m.d 2 4) (by simp) with h14729 | h14729
                                        · rcases p14722_3 (m.d 3 4) (by simp) with h14730 | h14730
                                          · linarith only [h14484, h14730, hlam]
                                          · linarith only [h14632, h14730, hlam]
                                        · linarith only [h14631, h14729, hlam]
                                      · linarith only [h14628, h14728, hlam]
                                    · linarith only [h14727, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14624, h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14624, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14624, h14629, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14633_1, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    rcases p14722_3 (m.d 0 4) (by simp) with h14740 | h14740
                                    · linarith only [h14740, h8811, hlam]
                                    · linarith only [h14486, h14740, hlam]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14484, h14629, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14633_1, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14629, h14632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14633_1, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    rcases p14722_3 (m.d 0 4) (by simp) with h14747 | h14747
                                    · linarith only [h13831, h14747, hlam]
                                    · linarith only [h14486, h14747, hlam]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14484, hlam, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14626, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14629, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14484, hc03, hc45, hlam, hphi, ht0b, ht5b, p14722_1]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14486, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14628, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14631, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [h14632, hlam, p14722_0]
                                  · have p14722_0 := h14722c.1
                                    have p14722_1 := h14722c.2.1
                                    have p14722_2 := h14722c.2.2.1
                                    have p14722_3 := h14722c.2.2.2
                                    linarith only [hlam, p14722_0]
                              · linarith only [h14632, h14719, hlam]
                            · linarith only [h14630, h14718, hlam]
                          · linarith only [h14627, h14717, hlam]
                        · linarith only [h14485, h14716, hlam]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14485, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14627, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14630, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [h14632, hlam, p14633_0]
                      · have p14633_0 := h14633c.1
                        have p14633_1 := h14633c.2.1
                        have p14633_2 := h14633c.2.2.1
                        have p14633_3 := h14633c.2.2.2
                        linarith only [hlam, p14633_0]
                    · rcases h3bigk with h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c | h14769c
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h7360, hlam, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h11548, hlam, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14773 | h14773
                        · rcases p14769_3 (m.d 1 3) (by simp) with h14774 | h14774
                          · rcases p14769_3 (m.d 2 3) (by simp) with h14775 | h14775
                            · rcases p14769_3 (m.d 3 4) (by simp) with h14776 | h14776
                              · linarith only [h14776, hlam, p14769_0]
                              · rcases p14769_3 (m.d 3 5) (by simp) with h14778 | h14778
                                · linarith only [h14485, h14778, hlam]
                                · linarith only [h14632, h14778, hlam]
                            · linarith only [h14629, h14775, hlam]
                          · linarith only [h14626, h14774, hlam]
                        · linarith only [h14773, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14784 | h14784
                        · rcases p14769_3 (m.d 1 3) (by simp) with h14785 | h14785
                          · rcases p14769_3 (m.d 2 3) (by simp) with h14786 | h14786
                            · rcases p14769_3 (m.d 3 4) (by simp) with h14787 | h14787
                              · linarith only [h14484, h14787, hlam]
                              · rcases p14769_3 (m.d 3 5) (by simp) with h14789 | h14789
                                · linarith only [h14789, hlam, p14769_0]
                                · rcases h4bigk with h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c | h14791c
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h8811, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h13831, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    rcases p14791_3 (m.d 0 4) (by simp) with h14795 | h14795
                                    · rcases p14791_3 (m.d 1 4) (by simp) with h14796 | h14796
                                      · rcases p14791_3 (m.d 2 4) (by simp) with h14797 | h14797
                                        · rcases p14791_3 (m.d 3 4) (by simp) with h14798 | h14798
                                          · linarith only [h14484, h14798, hlam]
                                          · rcases p14791_3 (m.d 4 5) (by simp) with h14800 | h14800
                                            · linarith only [h14486, h14800, hlam]
                                            · linarith only [h14632, h14800, hlam]
                                        · linarith only [h14629, h14797, hlam]
                                      · linarith only [h14626, h14796, hlam]
                                    · linarith only [h14484, h14795, hlam]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14484, h14487, h14632, h7360, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14624, h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14624, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    rcases p14791_3 (m.d 0 4) (by simp) with h14810 | h14810
                                    · linarith only [h14810, h8811, hlam]
                                    · linarith only [h14484, h14810, hlam]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14624, h14629, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14486, h14629, h14632, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    rcases p14791_3 (m.d 0 4) (by simp) with h14817 | h14817
                                    · linarith only [h13831, h14817, hlam]
                                    · linarith only [h14484, h14817, hlam]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14629, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14484, hlam, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14626, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14629, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14632, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14486, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14628, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14631, hlam, p14791_0]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [h14486, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p14791_1]
                                  · have p14791_0 := h14791c.1
                                    have p14791_1 := h14791c.2.1
                                    have p14791_2 := h14791c.2.2.1
                                    have p14791_3 := h14791c.2.2.2
                                    linarith only [hlam, p14791_0]
                            · linarith only [h14630, h14786, hlam]
                          · linarith only [h14627, h14785, hlam]
                        · linarith only [h14784, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14484, h14486, h14487, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14487, hlam, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14837 | h14837
                        · linarith only [h14837, h7360, hlam]
                        · linarith only [h14484, h14837, hlam]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14840 | h14840
                        · linarith only [h14840, h7360, hlam]
                        · linarith only [h14485, h14840, hlam]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14484, h14486, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14846 | h14846
                        · linarith only [h11548, h14846, hlam]
                        · linarith only [h14484, h14846, hlam]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14849 | h14849
                        · linarith only [h11548, h14849, hlam]
                        · linarith only [h14485, h14849, hlam]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14484, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14626, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14629, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14632, hlam, p14769_1]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14485, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14627, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [h14630, hlam, p14769_0]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        rcases p14769_3 (m.d 0 3) (by simp) with h14860 | h14860
                        · rcases p14769_3 (m.d 1 3) (by simp) with h14861 | h14861
                          · rcases p14769_3 (m.d 2 3) (by simp) with h14862 | h14862
                            · rcases p14769_3 (m.d 3 4) (by simp) with h14863 | h14863
                              · linarith only [h14632, h14863, hlam]
                              · rcases p14769_3 (m.d 3 5) (by simp) with h14865 | h14865
                                · rcases h4bigk with h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c | h14866c
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h8811, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h13831, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    rcases p14866_3 (m.d 0 4) (by simp) with h14870 | h14870
                                    · rcases p14866_3 (m.d 1 4) (by simp) with h14871 | h14871
                                      · rcases p14866_3 (m.d 2 4) (by simp) with h14872 | h14872
                                        · rcases p14866_3 (m.d 3 4) (by simp) with h14873 | h14873
                                          · linarith only [h14484, h14873, hlam]
                                          · rcases p14866_3 (m.d 4 5) (by simp) with h14875 | h14875
                                            · linarith only [h14486, h14875, hlam]
                                            · linarith only [h14632, h14875, hlam]
                                        · linarith only [h14629, h14872, hlam]
                                      · linarith only [h14626, h14871, hlam]
                                    · linarith only [h14484, h14870, hlam]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14484, h14632, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p14769_1, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14624, h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14624, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    rcases p14866_3 (m.d 0 4) (by simp) with h14885 | h14885
                                    · linarith only [h14885, h8811, hlam]
                                    · linarith only [h14484, h14885, hlam]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14624, h14629, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14769_1, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14486, h14629, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14769_1, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14629, h8811, hc01, hc23, hlam, hphi, ht12, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    rcases p14866_3 (m.d 0 4) (by simp) with h14892 | h14892
                                    · linarith only [h13831, h14892, hlam]
                                    · linarith only [h14484, h14892, hlam]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14629, h14632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14769_1, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14484, hlam, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14626, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14629, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14632, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14486, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14628, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14631, hlam, p14866_0]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [h14486, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p14866_1]
                                  · have p14866_0 := h14866c.1
                                    have p14866_1 := h14866c.2.1
                                    have p14866_2 := h14866c.2.2.1
                                    have p14866_3 := h14866c.2.2.2
                                    linarith only [hlam, p14866_0]
                                · linarith only [h14632, h14865, hlam]
                            · linarith only [h14629, h14862, hlam]
                          · linarith only [h14626, h14861, hlam]
                        · linarith only [h14484, h14860, hlam]
                      · have p14769_0 := h14769c.1
                        have p14769_1 := h14769c.2.1
                        have p14769_2 := h14769c.2.2.1
                        have p14769_3 := h14769c.2.2.2
                        linarith only [hlam, p14769_0]
                  · linarith only [h14484, h14486, h14487, h14624, h14631, h7360, h8811, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14485, h14487, h14630, h7360, hlam]
              · linarith only [h0, h14487, h14629, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h14486, h14628, h8811, hlam]
          · linarith only [h14485, h14627, h7360, hlam]
        · linarith only [h14484, h14626, h7360, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h14917 | h14917
    · rcases m.htr 1 2 4 (by decide) (by decide) with h14918 | h14918
      · rcases m.htr 1 3 4 (by decide) (by decide) with h14919 | h14919
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14920 | h14920
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14921 | h14921
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14922 | h14922
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14923 | h14923
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14924 | h14924
                  · linarith only [h0, h13831, h14486, h14917, h14922, h14924, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h13831, h14919, h14921, h14924, hc01, hc13, hlam, hphi]
                · linarith only [h0, h11548, h14485, h14917, h14923, h7360, hc01, hc12, hlam, hphi]
              · linarith only [h11548, h14484, h14922, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14929 | h14929
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14930 | h14930
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14931 | h14931
                  · linarith only [h14921, h14931, h8811, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14933 | h14933
                    · linarith only [h0, h13831, h14918, h14921, h14933, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h3bigk with h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c | h14935c
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h7360, hlam, p14935_1]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h11548, hlam, p14935_1]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h14939 | h14939
                        · rcases p14935_3 (m.d 1 3) (by simp) with h14940 | h14940
                          · rcases p14935_3 (m.d 2 3) (by simp) with h14941 | h14941
                            · rcases p14935_3 (m.d 3 4) (by simp) with h14942 | h14942
                              · linarith only [h14942, hlam, p14935_0]
                              · rcases p14935_3 (m.d 3 5) (by simp) with h14944 | h14944
                                · linarith only [h14485, h14944, hlam]
                                · linarith only [h14933, h14944, hlam]
                            · linarith only [h14929, h14941, hlam]
                          · linarith only [h14919, h14940, hlam]
                        · linarith only [h14939, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h14950 | h14950
                        · rcases p14935_3 (m.d 1 3) (by simp) with h14951 | h14951
                          · rcases p14935_3 (m.d 2 3) (by simp) with h14952 | h14952
                            · rcases p14935_3 (m.d 3 4) (by simp) with h14953 | h14953
                              · linarith only [h14484, h14953, hlam]
                              · rcases p14935_3 (m.d 3 5) (by simp) with h14955 | h14955
                                · linarith only [h14955, hlam, p14935_0]
                                · rcases h4bigk with h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c | h14957c
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h8811, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h13831, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h13831, h14918, h14921, hc34, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14486, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14921, hc04, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14921, hc24, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14921, hc34, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14921, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h0, h13831, hc01, hc24, hlam, hphi, ht12, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14918, hlam, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14918, h14921, hc34, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14931, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14484, hlam, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14919, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14929, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h14933, hlam, p14957_0]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h0, h13831, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hc14, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [h0, h13831, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hc34, hc45, hlam, hphi, p14957_1]
                                  · have p14957_0 := h14957c.1
                                    have p14957_1 := h14957c.2.1
                                    have p14957_2 := h14957c.2.2.1
                                    have p14957_3 := h14957c.2.2.2
                                    linarith only [hlam, p14957_0]
                            · linarith only [h14930, h14952, hlam]
                          · linarith only [h14920, h14951, hlam]
                        · linarith only [h14950, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h14986 | h14986
                        · linarith only [h14986, h7360, hlam]
                        · rcases p14935_3 (m.d 1 3) (by simp) with h14988 | h14988
                          · rcases p14935_3 (m.d 2 3) (by simp) with h14989 | h14989
                            · linarith only [h14917, h14989, hlam]
                            · linarith only [h11548, h14989, hlam]
                          · linarith only [h14988, h7360, hlam]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h0, h13831, h14917, h14930, h14931, hc01, hc12, hlam, hphi, p14935_1]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h14995 | h14995
                        · linarith only [h14995, h7360, hlam]
                        · linarith only [h14484, h14995, hlam]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h14998 | h14998
                        · linarith only [h14998, h7360, hlam]
                        · linarith only [h14485, h14998, hlam]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14485, h14917, h14933, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14935_1]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14917, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h15004 | h15004
                        · linarith only [h11548, h15004, hlam]
                        · linarith only [h14484, h15004, hlam]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        rcases p14935_3 (m.d 0 3) (by simp) with h15007 | h15007
                        · linarith only [h11548, h15007, hlam]
                        · linarith only [h14485, h15007, hlam]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14484, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14919, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14929, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14933, hlam, p14935_1]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14485, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14920, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h14930, hlam, p14935_0]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [h11548, h14485, h14917, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14935_1]
                      · have p14935_0 := h14935c.1
                        have p14935_1 := h14935c.2.1
                        have p14935_2 := h14935c.2.2.1
                        have p14935_3 := h14935c.2.2.2
                        linarith only [hlam, p14935_0]
                · linarith only [h11548, h14485, h14930, hlam]
              · linarith only [h11548, h14484, h14929, hlam]
          · linarith only [h11548, h14485, h14920, h7360, hc01, hc23, hlam, hphi, ht12]
        · linarith only [h11548, h14484, h14917, h14919, hlam]
      · linarith only [h0, h11548, h14917, h14918, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15025 | h15025
      · linarith only [h0, h13831, h14917, h15025, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h15027 | h15027
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15028 | h15028
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15029 | h15029
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15030 | h15030
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15031 | h15031
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15032 | h15032
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15033 | h15033
                    · linarith only [h0, h13831, h14484, h14486, h15033, h7360, hc01, hc13, hlam, hphi]
                    · rcases h3bigk with h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c | h15035c
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h7360, hlam, p15035_1]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h11548, hlam, p15035_1]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15039 | h15039
                        · rcases p15035_3 (m.d 1 3) (by simp) with h15040 | h15040
                          · rcases p15035_3 (m.d 2 3) (by simp) with h15041 | h15041
                            · rcases p15035_3 (m.d 3 4) (by simp) with h15042 | h15042
                              · linarith only [h15042, hlam, p15035_0]
                              · rcases p15035_3 (m.d 3 5) (by simp) with h15044 | h15044
                                · linarith only [h14485, h15044, hlam]
                                · linarith only [h15033, h15044, hlam]
                            · linarith only [h15030, h15041, hlam]
                          · linarith only [h15027, h15040, hlam]
                        · linarith only [h15039, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15050 | h15050
                        · rcases p15035_3 (m.d 1 3) (by simp) with h15051 | h15051
                          · rcases p15035_3 (m.d 2 3) (by simp) with h15052 | h15052
                            · rcases p15035_3 (m.d 3 4) (by simp) with h15053 | h15053
                              · linarith only [h14484, h15053, hlam]
                              · rcases p15035_3 (m.d 3 5) (by simp) with h15055 | h15055
                                · linarith only [h15055, hlam, p15035_0]
                                · rcases h4bigk with h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c | h15057c
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h8811, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h13831, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h14486, h15029, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h14486, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h8811, hc01, hc14, hlam, hphi, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15025, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    rcases p15057_3 (m.d 0 4) (by simp) with h15066 | h15066
                                    · linarith only [h15066, h8811, hlam]
                                    · linarith only [h14484, h15066, hlam]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h10295, h14486, h15025, h15030, hc01, hc23, hlam, hphi, ht12, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h0, h13831, h15030, hc01, hc23, hlam, hphi, ht12, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15030, h8811, hc01, hc23, hlam, hphi, ht12, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    rcases p15057_3 (m.d 0 4) (by simp) with h15073 | h15073
                                    · linarith only [h13831, h15073, hlam]
                                    · linarith only [h14484, h15073, hlam]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h0, h13831, h14486, h15030, hc01, hc23, hlam, hphi, ht12, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h14484, hlam, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15027, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15030, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15033, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h0, h13831, h15029, hc01, hc14, hlam, hphi, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15029, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15032, hlam, p15057_0]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [h15025, h15029, h15030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15057_1]
                                  · have p15057_0 := h15057c.1
                                    have p15057_1 := h15057c.2.1
                                    have p15057_2 := h15057c.2.2.1
                                    have p15057_3 := h15057c.2.2.2
                                    linarith only [hlam, p15057_0]
                            · linarith only [h15031, h15052, hlam]
                          · linarith only [h15028, h15051, hlam]
                        · linarith only [h15050, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15090 | h15090
                        · linarith only [h15090, h7360, hlam]
                        · rcases p15035_3 (m.d 1 3) (by simp) with h15092 | h15092
                          · rcases p15035_3 (m.d 2 3) (by simp) with h15093 | h15093
                            · rcases p15035_3 (m.d 3 4) (by simp) with h15094 | h15094
                              · linarith only [h15027, h15094, hlam]
                              · rcases p15035_3 (m.d 3 5) (by simp) with h15096 | h15096
                                · linarith only [h15028, h15096, hlam]
                                · rcases h4bigk with h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c | h15098c
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h8811, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h13831, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h14484, h14917, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15035_1, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h14486, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15025, h15030, h8811, hc01, hc23, hlam, hphi, ht12, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15025, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    rcases p15098_3 (m.d 0 4) (by simp) with h15107 | h15107
                                    · linarith only [h15107, h8811, hlam]
                                    · linarith only [h14484, h15107, hlam]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h0, h13831, h14486, h15025, h15030, hc01, hc23, hlam, hphi, ht12, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h0, h13831, h15030, hc01, hc23, hlam, hphi, ht12, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15030, h8811, hc01, hc23, hlam, hphi, ht12, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    rcases p15098_3 (m.d 0 4) (by simp) with h15114 | h15114
                                    · linarith only [h13831, h15114, hlam]
                                    · linarith only [h14484, h15114, hlam]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h0, h13831, h14486, h15030, hc01, hc23, hlam, hphi, ht12, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h14484, hlam, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15027, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15030, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15033, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h0, h13831, h15029, hc01, hc14, hlam, hphi, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15029, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15032, hlam, p15098_0]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [h15025, h15029, h15030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15098_1]
                                  · have p15098_0 := h15098c.1
                                    have p15098_1 := h15098c.2.1
                                    have p15098_2 := h15098c.2.2.1
                                    have p15098_3 := h15098c.2.2.2
                                    linarith only [hlam, p15098_0]
                            · linarith only [h11548, h15093, hlam]
                          · linarith only [h15092, h7360, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h14917, hlam, p15035_1]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15132 | h15132
                        · linarith only [h15132, h7360, hlam]
                        · linarith only [h14484, h15132, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15135 | h15135
                        · linarith only [h15135, h7360, hlam]
                        · linarith only [h14485, h15135, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15138 | h15138
                        · linarith only [h11548, h15138, hlam]
                        · rcases p15035_3 (m.d 1 3) (by simp) with h15140 | h15140
                          · linarith only [h14917, h15140, hlam]
                          · linarith only [h15140, h7360, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h7360, hc01, hc23, hlam, hphi, ht12, p15035_1]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15145 | h15145
                        · linarith only [h11548, h15145, hlam]
                        · linarith only [h14484, h15145, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15148 | h15148
                        · linarith only [h11548, h15148, hlam]
                        · linarith only [h14485, h15148, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h14484, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h15027, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h15030, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h15033, hlam, p15035_1]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h14485, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h15028, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [h15031, hlam, p15035_0]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        rcases p15035_3 (m.d 0 3) (by simp) with h15159 | h15159
                        · rcases p15035_3 (m.d 1 3) (by simp) with h15160 | h15160
                          · rcases p15035_3 (m.d 2 3) (by simp) with h15161 | h15161
                            · rcases p15035_3 (m.d 3 4) (by simp) with h15162 | h15162
                              · linarith only [h15033, h15162, hlam]
                              · rcases p15035_3 (m.d 3 5) (by simp) with h15164 | h15164
                                · rcases h4bigk with h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c | h15165c
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h8811, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h13831, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h14486, h15025, h15029, h15030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h14486, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15025, h15030, h8811, hc01, hc23, hlam, hphi, ht12, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15025, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    rcases p15165_3 (m.d 0 4) (by simp) with h15174 | h15174
                                    · linarith only [h15174, h8811, hlam]
                                    · linarith only [h14484, h15174, hlam]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h10295, h14486, h15025, h15030, hc01, hc23, hlam, hphi, ht12, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h0, h13831, h15030, hc01, hc23, hlam, hphi, ht12, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15030, h8811, hc01, hc23, hlam, hphi, ht12, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    rcases p15165_3 (m.d 0 4) (by simp) with h15181 | h15181
                                    · linarith only [h13831, h15181, hlam]
                                    · linarith only [h14484, h15181, hlam]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h14485, h14486, h15030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15035_1, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h14484, hlam, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15027, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15030, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15033, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h0, h13831, h15029, hc01, hc14, hlam, hphi, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15029, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15032, hlam, p15165_0]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [h15025, h15029, h15030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15165_1]
                                  · have p15165_0 := h15165c.1
                                    have p15165_1 := h15165c.2.1
                                    have p15165_2 := h15165c.2.2.1
                                    have p15165_3 := h15165c.2.2.2
                                    linarith only [hlam, p15165_0]
                                · linarith only [h15033, h15164, hlam]
                            · linarith only [h15030, h15161, hlam]
                          · linarith only [h15027, h15160, hlam]
                        · linarith only [h14484, h15159, hlam]
                      · have p15035_0 := h15035c.1
                        have p15035_1 := h15035c.2.1
                        have p15035_2 := h15035c.2.2.1
                        have p15035_3 := h15035c.2.2.2
                        linarith only [hlam, p15035_0]
                  · linarith only [h15025, h15029, h15032, hlam]
                · linarith only [h14485, h14917, h15031, h7360, hlam]
              · linarith only [h0, h13831, h14486, h14917, h15027, h15029, h15030, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15203 | h15203
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15204 | h15204
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15205 | h15205
                  · linarith only [h15029, h15203, h15205, h8811, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h15025, h15205, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h11548, h14485, h15204, h7360, hc01, hc13, hlam, hphi]
              · linarith only [h14484, h14917, h15203, h7360, hlam]
          · linarith only [h14485, h15028, h7360, hlam]
        · linarith only [h14484, h15027, h7360, hlam]

end R2N4
