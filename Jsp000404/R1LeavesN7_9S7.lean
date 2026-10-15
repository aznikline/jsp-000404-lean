import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7366000 in
set_option maxHeartbeats 7366000 in
theorem r1l7_13_24_L_I_H_I_s4 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_13_24_L_I_H_I_s5 m hb3 hb4 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3459 | h3459
    · linarith only [h3459, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3461 | h3461
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3462 | h3462
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3463 | h3463
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3464 | h3464
            · linarith only [h0, h3464, h5, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3466 | h3466
              · linarith only [h1, h3459, h3461, h3466, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3468 | h3468
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3469 | h3469
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3470 | h3470
                    · linarith only [h3459, h3470, h4, h5, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3472 | h3472
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3473 | h3473
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3474 | h3474
                          · rcases h3bigk with h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c | h3475c
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3463, h3470, h3472, h3474, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3475_1]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3470, h3472, h3474, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3475_1]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3459, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              rcases p3475_3 (m.d 0 3) (by simp) with h3480 | h3480
                              · rcases p3475_3 (m.d 1 3) (by simp) with h3481 | h3481
                                · linarith only [h1, h3481, hlam]
                                · linarith only [h3468, h3481, hlam]
                              · linarith only [h3480, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h1, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h1, h3472, h3474, hc01, hc45, hlam, hphi, ht0b, ht5b, p3475_1]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3466, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              rcases p3475_3 (m.d 0 3) (by simp) with h3489 | h3489
                              · rcases p3475_3 (m.d 1 3) (by simp) with h3490 | h3490
                                · rcases p3475_3 (m.d 2 3) (by simp) with h3491 | h3491
                                  · linarith only [h3463, h3491, hlam]
                                  · linarith only [h3472, h3491, hlam]
                                · linarith only [h3490, hlam, p3475_0]
                              · linarith only [h3461, h3489, hlam]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h4, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3463, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3470, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3470, h3474, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3475_1]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              rcases p3475_3 (m.d 0 3) (by simp) with h3501 | h3501
                              · linarith only [h3501, hlam, p3475_0]
                              · rcases p3475_3 (m.d 1 3) (by simp) with h3503 | h3503
                                · linarith only [h3466, h3503, hlam]
                                · rcases p3475_3 (m.d 2 3) (by simp) with h3505 | h3505
                                  · linarith only [h3470, h3505, hlam]
                                  · rcases p3475_3 (m.d 3 4) (by simp) with h3507 | h3507
                                    · rcases p3475_3 (m.d 3 5) (by simp) with h3508 | h3508
                                      · linarith only [h3474, h3508, hlam]
                                      · rcases h4bigk with h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c | h3510c
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3463, h3464, h3472, h3474, hc04, hc45, hlam, hphi, ht0b, ht5b, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h5, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3459, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          rcases p3510_3 (m.d 0 4) (by simp) with h3515 | h3515
                                          · rcases p3510_3 (m.d 1 4) (by simp) with h3516 | h3516
                                            · linarith only [h2, h3516, hlam]
                                            · linarith only [h3469, h3516, hlam]
                                          · linarith only [h3515, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h2, hlam, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3464, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3466, hlam, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3470, h5, hc02, hc34, hlam, hphi, ht23, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3463, h3464, h3470, h3472, h3474, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3470, hlam, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          rcases p3510_3 (m.d 0 4) (by simp) with h3529 | h3529
                                          · linarith only [h3529, h5, hlam]
                                          · linarith only [h3462, h3529, hlam]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h0, h3463, h3472, h3474, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3463, h3464, h3472, h3474, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h0, h3463, h3472, h3474, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3510_1]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          rcases p3510_3 (m.d 0 4) (by simp) with h3536 | h3536
                                          · linarith only [h3459, h3536, hlam]
                                          · linarith only [h3462, h3536, hlam]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3462, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3469, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3473, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [h3474, hlam, p3510_0]
                                        · have p3510_0 := h3510c.1
                                          have p3510_1 := h3510c.2.1
                                          have p3510_2 := h3510c.2.2.1
                                          have p3510_3 := h3510c.2.2.2
                                          linarith only [hlam, p3510_0]
                                    · linarith only [h3507, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              rcases p3475_3 (m.d 0 3) (by simp) with h3545 | h3545
                              · linarith only [h3459, h3545, hlam]
                              · linarith only [h1, h3545, hlam]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              rcases p3475_3 (m.d 0 3) (by simp) with h3548 | h3548
                              · linarith only [h3459, h3548, hlam]
                              · linarith only [h3548, h4, hlam]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h0, h3463, h3470, h3472, h5, hlam, p3475_2]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3461, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3468, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3472, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [h3474, hlam, p3475_0]
                            · have p3475_0 := h3475c.1
                              have p3475_1 := h3475c.2.1
                              have p3475_2 := h3475c.2.2.1
                              have p3475_3 := h3475c.2.2.2
                              linarith only [hlam, p3475_0]
                          · linarith only [h0, h3463, h3470, h3472, h3474, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h1, h3463, h3468, h3469, h3472, h3473, h5, hc03, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h3461, h3470, h3472, h4, h5, hc23, hc34, hlam, hphi]
                  · linarith only [h3459, h3462, h3463, h3464, h3469, hc23, hc34, hlam, hphi]
                · linarith only [h3459, h3461, h3468, hc13, hc34, hlam, hphi]
          · linarith only [h3463, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h3461, h3462, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3565 | h3565
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3566 | h3566
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3567 | h3567
            · linarith only [h0, h3567, h5, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3569 | h3569
              · linarith only [h1, h3459, h3569, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3571 | h3571
                · linarith only [h1, h3461, h3571, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3573 | h3573
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3574 | h3574
                    · linarith only [h0, h3459, h3566, h3574, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3576 | h3576
                      · linarith only [h1, h3461, h3566, h3576, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3578 | h3578
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3579 | h3579
                          · rcases h3bigk with h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c | h3580c
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3461, h3566, hc23, hc35, hlam, hphi, p3580_1]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3574, h4, h5, hc23, hc34, hlam, hphi, p3580_1]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3459, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3461, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h1, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h1, h3574, h4, h5, hc23, hc34, hlam, hphi, p3580_1]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3569, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3571, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h4, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3566, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3574, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3576, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              rcases p3580_3 (m.d 0 3) (by simp) with h3596 | h3596
                              · linarith only [h3596, hlam, p3580_0]
                              · rcases p3580_3 (m.d 1 3) (by simp) with h3598 | h3598
                                · linarith only [h3569, h3598, hlam]
                                · rcases p3580_3 (m.d 2 3) (by simp) with h3600 | h3600
                                  · linarith only [h3574, h3600, hlam]
                                  · rcases p3580_3 (m.d 3 4) (by simp) with h3602 | h3602
                                    · rcases p3580_3 (m.d 3 5) (by simp) with h3603 | h3603
                                      · linarith only [h3579, h3603, hlam]
                                      · linarith only [h3461, h3603, hlam]
                                    · linarith only [h3602, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              rcases p3580_3 (m.d 0 3) (by simp) with h3607 | h3607
                              · linarith only [h3459, h3607, hlam]
                              · linarith only [h1, h3607, hlam]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              rcases p3580_3 (m.d 0 3) (by simp) with h3610 | h3610
                              · linarith only [h3459, h3610, hlam]
                              · linarith only [h3610, h4, hlam]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3461, hc03, hc34, hlam, hphi, p3580_1]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              rcases p3580_3 (m.d 0 3) (by simp) with h3615 | h3615
                              · linarith only [h3615, hlam, p3580_0]
                              · rcases p3580_3 (m.d 1 3) (by simp) with h3617 | h3617
                                · linarith only [h3571, h3617, hlam]
                                · rcases p3580_3 (m.d 2 3) (by simp) with h3619 | h3619
                                  · linarith only [h3576, h3619, hlam]
                                  · rcases p3580_3 (m.d 3 4) (by simp) with h3621 | h3621
                                    · rcases p3580_3 (m.d 3 5) (by simp) with h3622 | h3622
                                      · rcases h4bigk with h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c | h3623c
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3567, h3574, h5, hc12, hc34, hlam, hphi, ht23, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h5, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3459, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          rcases p3623_3 (m.d 0 4) (by simp) with h3628 | h3628
                                          · rcases p3623_3 (m.d 1 4) (by simp) with h3629 | h3629
                                            · linarith only [h2, h3629, hlam]
                                            · linarith only [h3573, h3629, hlam]
                                          · linarith only [h3628, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h2, hlam, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3567, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3569, hlam, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3574, h5, hc02, hc34, hlam, hphi, ht23, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3566, h3567, h3574, hc23, hc34, hlam, hphi, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3574, hlam, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          rcases p3623_3 (m.d 0 4) (by simp) with h3642 | h3642
                                          · linarith only [h3642, h5, hlam]
                                          · linarith only [h3565, h3642, hlam]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h0, h3566, h5, hc23, hc34, hlam, hphi, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3566, h3567, hc23, hc34, hlam, hphi, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h0, h3566, h5, hc23, hc34, hlam, hphi, p3623_1]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          rcases p3623_3 (m.d 0 4) (by simp) with h3649 | h3649
                                          · linarith only [h3459, h3649, hlam]
                                          · linarith only [h3565, h3649, hlam]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3565, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3573, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3578, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [h3579, hlam, p3623_0]
                                        · have p3623_0 := h3623c.1
                                          have p3623_1 := h3623c.2.1
                                          have p3623_2 := h3623c.2.2.1
                                          have p3623_3 := h3623c.2.2.2
                                          linarith only [hlam, p3623_0]
                                      · linarith only [h3622, hlam, p3580_0]
                                    · linarith only [h3459, h3621, hlam]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              rcases p3580_3 (m.d 0 3) (by simp) with h3659 | h3659
                              · linarith only [h3461, h3659, hlam]
                              · linarith only [h1, h3659, hlam]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              rcases p3580_3 (m.d 0 3) (by simp) with h3662 | h3662
                              · linarith only [h3461, h3662, hlam]
                              · linarith only [h3662, h4, hlam]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [h3579, hlam, p3580_0]
                            · have p3580_0 := h3580c.1
                              have p3580_1 := h3580c.2.1
                              have p3580_2 := h3580c.2.2.1
                              have p3580_3 := h3580c.2.2.2
                              linarith only [hlam, p3580_0]
                          · linarith only [h3459, h3565, h3579, hlam]
                        · linarith only [h2, h3573, h3578, h5, hlam]
                  · linarith only [h3459, h3565, h3566, h3567, h3573, hc23, hc34, hlam, hphi]
          · linarith only [h3566, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3671 | h3671
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3672 | h3672
            · linarith only [h0, h3672, h5, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3674 | h3674
              · linarith only [h1, h3459, h3674, h4, h5, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3676 | h3676
                · linarith only [h1, h3461, h3676, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3678 | h3678
                  · linarith only [h2, h3565, h3678, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3680 | h3680
                    · linarith only [h0, h3459, h3671, h3680, h5, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3682 | h3682
                      · linarith only [h0, h3461, h3565, h3671, h3682, h5, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3684 | h3684
                        · linarith only [h0, h3565, h3671, h3680, h3684, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h3671, h3684, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h3671, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_13_24_L_I_H_I_s4 m hb3 hb4 h0 h1 h2 h3 h4

end R2N4
