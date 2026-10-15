import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S27
import Jsp000404.R1LeavesN7_4S28

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12204000 in
set_option maxHeartbeats 12204000 in
theorem r1l7_11_23_L_I_H_I_s12_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h12794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h12795 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h13394 | h13394
  · rcases m.htr 0 2 4 (by decide) (by decide) with h13395 | h13395
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13396 | h13396
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13397 | h13397
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13398 | h13398
          · linarith only [h12794, h12795, h13398, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13400 | h13400
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13401 | h13401
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13402 | h13402
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13403 | h13403
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13404 | h13404
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13405 | h13405
                      · linarith only [h12794, h12795, h13398, h13404, h13405, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13407 | h13407
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13408 | h13408
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13409 | h13409
                            · linarith only [h12794, h12795, h13401, h13405, h13409, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13411 | h13411
                              · linarith only [h12795, h13394, h13405, h13407, h13411, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h1bigk with h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h0, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h11385, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h12795, h13401, h13405, h13407, hc34, hc45, hlam, hphi, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h12795, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  rcases p13413_3 (m.d 0 1) (by simp) with h13419 | h13419
                                  · linarith only [h13419, hlam, p13413_0]
                                  · rcases p13413_3 (m.d 1 2) (by simp) with h13421 | h13421
                                    · rcases p13413_3 (m.d 1 3) (by simp) with h13422 | h13422
                                      · linarith only [h13400, h13422, hlam]
                                      · linarith only [h11385, h13422, hlam]
                                    · linarith only [h13421, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h11385, hc01, hc12, hlam, hphi, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  rcases p13413_3 (m.d 0 1) (by simp) with h13428 | h13428
                                  · linarith only [h0, h13428, hlam]
                                  · linarith only [h12794, h13428, hlam]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h12795, hc01, hc12, hlam, hphi, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  rcases p13413_3 (m.d 0 1) (by simp) with h13432 | h13432
                                  · linarith only [h13432, hlam, p13413_0]
                                  · rcases p13413_3 (m.d 1 2) (by simp) with h13434 | h13434
                                    · rcases p13413_3 (m.d 1 3) (by simp) with h13435 | h13435
                                      · rcases p13413_3 (m.d 1 4) (by simp) with h13436 | h13436
                                        · linarith only [h13403, h13436, hlam]
                                        · rcases p13413_3 (m.d 1 5) (by simp) with h13438 | h13438
                                          · linarith only [h13404, h13438, hlam]
                                          · linarith only [h12795, h13438, hlam]
                                      · linarith only [h13435, hlam, p13413_0]
                                    · linarith only [h0, h13434, hlam]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h13400, hlam, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  rcases p13413_3 (m.d 0 1) (by simp) with h13445 | h13445
                                  · linarith only [h11385, h13445, hlam]
                                  · linarith only [h12794, h13445, hlam]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h12794, h12795, h13401, h13407, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h12794, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h13401, hlam, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h13403, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h13405, hlam, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h12794, h13401, h13405, h13407, hc34, hc45, hlam, hphi, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h13402, hlam, p13413_1]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [h13404, hlam, p13413_0]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  rcases p13413_3 (m.d 0 1) (by simp) with h13457 | h13457
                                  · linarith only [h12795, h13457, hlam]
                                  · linarith only [h12794, h13457, hlam]
                                · have p13413_0 := h13413c.1
                                  have p13413_1 := h13413c.2.1
                                  have p13413_2 := h13413c.2.2.1
                                  have p13413_3 := h13413c.2.2.2
                                  linarith only [hlam, p13413_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13461 | h13461
                            · linarith only [h12794, h12795, h13401, h13405, h13461, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13463 | h13463
                              · linarith only [h11385, h12795, h13397, h13400, h13405, h13407, h13408, h13463, hc01, hc12, hlam, hphi]
                              · rcases h1bigk with h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h0, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h11385, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h12795, h13401, h13405, h13407, hc34, hc45, hlam, hphi, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h12795, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  rcases p13465_3 (m.d 0 1) (by simp) with h13471 | h13471
                                  · linarith only [h13471, hlam, p13465_0]
                                  · rcases p13465_3 (m.d 1 2) (by simp) with h13473 | h13473
                                    · rcases p13465_3 (m.d 1 3) (by simp) with h13474 | h13474
                                      · linarith only [h13400, h13474, hlam]
                                      · linarith only [h11385, h13474, hlam]
                                    · linarith only [h13473, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h11385, h13397, h13408, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  rcases p13465_3 (m.d 0 1) (by simp) with h13480 | h13480
                                  · linarith only [h0, h13480, hlam]
                                  · linarith only [h12794, h13480, hlam]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h12795, hc01, hc12, hlam, hphi, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  rcases p13465_3 (m.d 0 1) (by simp) with h13484 | h13484
                                  · linarith only [h13484, hlam, p13465_0]
                                  · rcases p13465_3 (m.d 1 2) (by simp) with h13486 | h13486
                                    · rcases p13465_3 (m.d 1 3) (by simp) with h13487 | h13487
                                      · rcases p13465_3 (m.d 1 4) (by simp) with h13488 | h13488
                                        · linarith only [h13403, h13488, hlam]
                                        · rcases p13465_3 (m.d 1 5) (by simp) with h13490 | h13490
                                          · linarith only [h13404, h13490, hlam]
                                          · linarith only [h12795, h13490, hlam]
                                      · linarith only [h13487, hlam, p13465_0]
                                    · linarith only [h0, h13486, hlam]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h13400, hlam, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  rcases p13465_3 (m.d 0 1) (by simp) with h13497 | h13497
                                  · linarith only [h11385, h13497, hlam]
                                  · linarith only [h12794, h13497, hlam]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h12795, h13397, h13407, h13408, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h12794, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h13401, hlam, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h13403, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h13405, hlam, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h12794, h13401, h13405, h13407, hc34, hc45, hlam, hphi, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h13402, hlam, p13465_1]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [h13404, hlam, p13465_0]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  rcases p13465_3 (m.d 0 1) (by simp) with h13509 | h13509
                                  · linarith only [h12795, h13509, hlam]
                                  · linarith only [h12794, h13509, hlam]
                                · have p13465_0 := h13465c.1
                                  have p13465_1 := h13465c.2.1
                                  have p13465_2 := h13465c.2.2.1
                                  have p13465_3 := h13465c.2.2.2
                                  linarith only [hlam, p13465_0]
                        · linarith only [h12794, h12795, h13403, h13405, h13407, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h11385, h12794, h13397, h13404, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h11385, h13396, h13403, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13516 | h13516
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13517 | h13517
                    · linarith only [h13400, h13402, h13517, hlam]
                    · linarith only [h11385, h13397, h13517, hlam]
                  · linarith only [h11385, h13396, h13516, hlam]
              · linarith only [h0, h13395, h13401, hlam]
            · linarith only [h0, h13394, h13400, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13523 | h13523
          · linarith only [h11385, h12794, h13397, h13523, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13525 | h13525
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13526 | h13526
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13527 | h13527
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13528 | h13528
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13529 | h13529
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13530 | h13530
                      · linarith only [h11385, h12794, h13397, h13523, h13525, h13529, h13530, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13532 | h13532
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13533 | h13533
                          · linarith only [h13394, h13397, h13533, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13535 | h13535
                            · linarith only [h11385, h12794, h13397, h13525, h13526, h13529, h13530, h13535, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13537 | h13537
                              · linarith only [h11385, h12794, h13397, h13526, h13529, h13530, h13532, h13537, hlam]
                              · rcases h1bigk with h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h0, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, h13397, h13525, h13526, h13529, h13532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h12795, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  rcases p13539_3 (m.d 0 1) (by simp) with h13545 | h13545
                                  · linarith only [h13545, hlam, p13539_0]
                                  · rcases p13539_3 (m.d 1 2) (by simp) with h13547 | h13547
                                    · rcases p13539_3 (m.d 1 3) (by simp) with h13548 | h13548
                                      · linarith only [h13525, h13548, hlam]
                                      · linarith only [h11385, h13548, hlam]
                                    · linarith only [h13547, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, h13397, h13529, hc01, hc12, hlam, hphi, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, h12794, h13397, h13525, h13529, hlam, p13539_2]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, h12794, h13397, h13526, h13529, h13532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  rcases p13539_3 (m.d 0 1) (by simp) with h13556 | h13556
                                  · linarith only [h13556, hlam, p13539_0]
                                  · rcases p13539_3 (m.d 1 2) (by simp) with h13558 | h13558
                                    · rcases p13539_3 (m.d 1 3) (by simp) with h13559 | h13559
                                      · rcases p13539_3 (m.d 1 4) (by simp) with h13560 | h13560
                                        · linarith only [h13528, h13560, hlam]
                                        · rcases p13539_3 (m.d 1 5) (by simp) with h13562 | h13562
                                          · linarith only [h13529, h13562, hlam]
                                          · linarith only [h12795, h13562, hlam]
                                      · linarith only [h13559, hlam, p13539_0]
                                    · linarith only [h0, h13558, hlam]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h13525, hlam, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, h12794, h13397, h13529, hlam, p13539_2]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h11385, h12794, h13397, h13526, h13529, h13532, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h12794, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h13526, hlam, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h13528, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h13530, hlam, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h12794, h13526, h13530, h13532, hc34, hc45, hlam, hphi, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h13527, hlam, p13539_1]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [h13529, hlam, p13539_0]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  rcases p13539_3 (m.d 0 1) (by simp) with h13579 | h13579
                                  · linarith only [h12795, h13579, hlam]
                                  · linarith only [h12794, h13579, hlam]
                                · have p13539_0 := h13539c.1
                                  have p13539_1 := h13539c.2.1
                                  have p13539_2 := h13539c.2.2.1
                                  have p13539_3 := h13539c.2.2.2
                                  linarith only [hlam, p13539_0]
                        · linarith only [h13396, h13397, h13532, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13584 | h13584
                      · linarith only [h11385, h12794, h13529, h13584, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13586 | h13586
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13587 | h13587
                          · linarith only [h11385, h13529, h13587, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13589 | h13589
                            · linarith only [h11385, h12794, h13526, h13529, h13584, h13589, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13591 | h13591
                              · linarith only [h11385, h12794, h13526, h13529, h13584, h13586, h13591, hlam]
                              · linarith only [h11385, h12794, h13526, h13529, h13586, h13591, hc34, hc45, hlam, hphi]
                        · linarith only [h11385, h13396, h13529, h13586, hc23, hc35, hlam, hphi]
                  · linarith only [h11385, h12794, h13396, h13528, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13596 | h13596
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13597 | h13597
                    · linarith only [h11385, h12794, h13397, h13525, h13526, h13527, h13597, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13599 | h13599
                      · linarith only [h11385, h12794, h13523, h13597, h13599, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13601 | h13601
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13602 | h13602
                          · linarith only [h11385, h13597, h13602, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13604 | h13604
                            · linarith only [h0, h12794, h13526, h13527, h13599, h13604, hlam]
                            · linarith only [h11385, h12794, h13525, h13527, h13604, hc14, hc45, hlam, hphi]
                        · linarith only [h11385, h13396, h13597, h13601, hc23, hc35, hlam, hphi]
                  · linarith only [h11385, h12794, h13396, h13596, hlam]
              · linarith only [h0, h13395, h13526, hlam]
            · linarith only [h0, h13394, h13525, hlam]
      · linarith only [h11385, h12794, h13396, hlam]
    · linarith only [h0, h12794, h13395, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h13613 | h13613
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13614 | h13614
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13615 | h13615
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13616 | h13616
          · linarith only [h12794, h12795, h13616, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13618 | h13618
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13619 | h13619
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13620 | h13620
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13621 | h13621
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13622 | h13622
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13623 | h13623
                      · linarith only [h0, h12794, h13394, h13616, h13618, h13623, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13625 | h13625
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13626 | h13626
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13627 | h13627
                            · linarith only [h0, h12794, h13394, h13618, h13619, h13623, h13627, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13629 | h13629
                              · linarith only [h12794, h12795, h13619, h13623, h13625, h13629, hlam]
                              · rcases h1bigk with h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c | h13631c
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h0, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h11385, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h0, h13394, h13618, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h12795, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  rcases p13631_3 (m.d 0 1) (by simp) with h13637 | h13637
                                  · linarith only [h13637, hlam, p13631_0]
                                  · rcases p13631_3 (m.d 1 2) (by simp) with h13639 | h13639
                                    · rcases p13631_3 (m.d 1 3) (by simp) with h13640 | h13640
                                      · linarith only [h13618, h13640, hlam]
                                      · linarith only [h11385, h13640, hlam]
                                    · linarith only [h13639, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h0, h13394, h13618, hc01, hc12, hlam, hphi, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h0, h12794, h13394, h13618, hlam, p13631_2]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h12794, h12795, h13619, h13625, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  rcases p13631_3 (m.d 0 1) (by simp) with h13648 | h13648
                                  · linarith only [h13648, hlam, p13631_0]
                                  · rcases p13631_3 (m.d 1 2) (by simp) with h13650 | h13650
                                    · rcases p13631_3 (m.d 1 3) (by simp) with h13651 | h13651
                                      · rcases p13631_3 (m.d 1 4) (by simp) with h13652 | h13652
                                        · linarith only [h13621, h13652, hlam]
                                        · rcases p13631_3 (m.d 1 5) (by simp) with h13654 | h13654
                                          · linarith only [h13622, h13654, hlam]
                                          · linarith only [h12795, h13654, hlam]
                                      · linarith only [h13651, hlam, p13631_0]
                                    · linarith only [h0, h13650, hlam]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h13618, hlam, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  rcases p13631_3 (m.d 0 1) (by simp) with h13661 | h13661
                                  · linarith only [h11385, h13661, hlam]
                                  · linarith only [h12794, h13661, hlam]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h12794, h12795, h13619, h13625, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h12794, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h13619, hlam, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h13621, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h13623, hlam, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h12794, h13619, h13623, h13625, hc34, hc45, hlam, hphi, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h13620, hlam, p13631_1]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [h13622, hlam, p13631_0]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  rcases p13631_3 (m.d 0 1) (by simp) with h13673 | h13673
                                  · linarith only [h12795, h13673, hlam]
                                  · linarith only [h12794, h13673, hlam]
                                · have p13631_0 := h13631c.1
                                  have p13631_1 := h13631c.2.1
                                  have p13631_2 := h13631c.2.2.1
                                  have p13631_3 := h13631c.2.2.2
                                  linarith only [hlam, p13631_0]
                          · linarith only [h0, h12794, h13394, h13615, h13619, h13625, h13626, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h12794, h13394, h13614, h13619, h13625, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h11385, h13615, h13622, hlam]
                  · linarith only [h13394, h13614, h13618, h13621, hlam]
                · linarith only [h0, h12794, h13394, h13618, h13619, h13620, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h12794, h13394, h13618, h13619, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13683 | h13683
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13684 | h13684
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13685 | h13685
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13686 | h13686
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13687 | h13687
                      · linarith only [h12794, h12795, h13618, h13684, h13687, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13689 | h13689
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13690 | h13690
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13691 | h13691
                            · linarith only [h12794, h12795, h13683, h13687, h13691, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13693 | h13693
                              · linarith only [h12794, h12795, h13683, h13687, h13689, h13693, hlam]
                              · rcases h1bigk with h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c | h13695c
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h0, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h11385, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h12795, h13618, h13683, h13684, h13689, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h12795, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13618, hc01, hc23, hlam, hphi, ht12, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13618, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  rcases p13695_3 (m.d 0 1) (by simp) with h13704 | h13704
                                  · linarith only [h0, h13704, hlam]
                                  · linarith only [h12794, h13704, hlam]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h12794, h12795, h13618, h13683, h13689, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  rcases p13695_3 (m.d 0 1) (by simp) with h13708 | h13708
                                  · linarith only [h13708, hlam, p13695_0]
                                  · rcases p13695_3 (m.d 1 2) (by simp) with h13710 | h13710
                                    · linarith only [h13618, h13710, hlam]
                                    · linarith only [h0, h13710, hlam]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h0, h12794, h13618, h13683, h13689, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  rcases p13695_3 (m.d 0 1) (by simp) with h13715 | h13715
                                  · linarith only [h11385, h13715, hlam]
                                  · linarith only [h12794, h13715, hlam]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h12794, h12795, h13683, h13689, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h12794, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13683, hlam, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13685, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13687, hlam, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h12794, h13683, h13687, h13689, hc34, hc45, hlam, hphi, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13684, hlam, p13695_1]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [h13686, hlam, p13695_0]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  rcases p13695_3 (m.d 0 1) (by simp) with h13727 | h13727
                                  · linarith only [h12795, h13727, hlam]
                                  · linarith only [h12794, h13727, hlam]
                                · have p13695_0 := h13695c.1
                                  have p13695_1 := h13695c.2.1
                                  have p13695_2 := h13695c.2.2.1
                                  have p13695_3 := h13695c.2.2.2
                                  linarith only [hlam, p13695_0]
                          · linarith only [h0, h12794, h13618, h13683, h13689, h13690, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h13618, h13689, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11385, h12794, h12795, h13615, h13618, h13683, h13684, h13686, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h11385, h13614, h13685, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13735 | h13735
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13736 | h13736
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13737 | h13737
                      · linarith only [h0, h12794, h13684, h13737, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13739 | h13739
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13740 | h13740
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13741 | h13741
                            · linarith only [h0, h12794, h13683, h13684, h13737, h13741, hlam]
                            · linarith only [h0, h12794, h13684, h13741, hc14, hc45, hlam, hphi]
                          · linarith only [h0, h12794, h13394, h13615, h13683, h13739, h13740, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h13618, h13739, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11385, h13615, h13736, hlam]
                  · linarith only [h11385, h13614, h13735, hlam]
              · linarith only [h0, h13613, h13683, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13749 | h13749
          · linarith only [h12794, h12795, h13749, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13751 | h13751
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13752 | h13752
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13753 | h13753
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13754 | h13754
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13755 | h13755
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13756 | h13756
                      · linarith only [h0, h12794, h13749, h13756, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13758 | h13758
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13759 | h13759
                          · linarith only [h0, h12794, h13394, h13615, h13751, h13752, h13758, h13759, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h12794, h13394, h13752, h13755, h13758, h13759, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h12794, h13394, h13614, h13615, h13758, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13763 | h13763
                      · linarith only [h11385, h12794, h13749, h13755, h13763, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13765 | h13765
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13766 | h13766
                          · linarith only [h13751, h13755, h13766, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13768 | h13768
                            · linarith only [h0, h12794, h13394, h13751, h13752, h13755, h13763, h13768, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13770 | h13770
                              · linarith only [h0, h12794, h13394, h13751, h13752, h13755, h13763, h13765, h13770, hlam]
                              · linarith only [h0, h12794, h13394, h13751, h13752, h13755, h13765, h13770, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h12794, h13394, h13614, h13752, h13765, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h12794, h13394, h13614, h13751, h13754, hlam]
                · linarith only [h0, h12794, h13394, h13751, h13752, h13753, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h12794, h13394, h13751, h13752, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13777 | h13777
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13778 | h13778
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13779 | h13779
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13780 | h13780
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13781 | h13781
                      · linarith only [h0, h12794, h13751, h13781, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13783 | h13783
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13784 | h13784
                          · linarith only [h0, h13394, h13615, h13751, h13778, h13784, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h12794, h13751, h13777, h13783, h13784, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h13394, h13615, h13751, h13778, h13780, h13783, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h13751, h13778, h13780, hlam]
                  · linarith only [h0, h12794, h13614, h13751, h13777, h13779, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13790 | h13790
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13791 | h13791
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13792 | h13792
                      · linarith only [h0, h12794, h13778, h13792, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13794 | h13794
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13795 | h13795
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13796 | h13796
                            · linarith only [h0, h12794, h13394, h13615, h13777, h13791, h13792, h13796, hlam]
                            · linarith only [h0, h12794, h13777, h13778, h13794, h13796, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h12794, h13751, h13777, h13791, h13794, h13795, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h12794, h13394, h13615, h13751, h13777, h13791, h13794, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13801 | h13801
                      · linarith only [h0, h12794, h13749, h13778, h13801, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13803 | h13803
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13804 | h13804
                          · linarith only [h0, h13751, h13791, h13804, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h12794, h13751, h13777, h13803, h13804, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h12794, h13751, h13777, h13803, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h12794, h13614, h13751, h13777, h13790, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h13613, h13777, hlam]
      · linarith only [h11385, h12794, h13614, hlam]
    · linarith only [h0, h12794, h13613, hlam]

set_option maxHeartbeats 12204000 in
set_option maxHeartbeats 12204000 in
theorem r1l7_11_23_L_I_H_I_s12_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h12794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h12795 | h12795
  · exact r1l7_11_23_L_I_H_I_s12_x0_x0 m hb1 hb3 hg0 hg11385 h12794 h12795
  · exact r1l7_11_23_L_I_H_I_s12_x0_x1 m hb1 hb3 hg0 hg11385 h12794 h12795

set_option maxHeartbeats 12204000 in
set_option maxHeartbeats 12204000 in
theorem r1l7_11_23_L_I_H_I_s12_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  exact r1l7_11_23_L_I_H_I_s13 m hb1 hb3 h0 h11385 h12794

set_option maxHeartbeats 12204000 in
set_option maxHeartbeats 12204000 in
theorem r1l7_11_23_L_I_H_I_s12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h12794 | h12794
  · exact r1l7_11_23_L_I_H_I_s12_x0 m hb1 hb3 hg0 hg11385 h12794
  · exact r1l7_11_23_L_I_H_I_s12_x1 m hb1 hb3 hg0 hg11385 h12794

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h11387 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h11388 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11389 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11390 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h11391 | h11391
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11392 | h11392
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11393 | h11393
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11394 | h11394
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11395 | h11395
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11396 | h11396
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11397 | h11397
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11398 | h11398
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11399 | h11399
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11400 | h11400
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11401 | h11401
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11402 | h11402
                        · linarith only [h0, h11385, h11393, h11399, h11402, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h11385, h11396, h11398, h11402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h11385, h11396, h11398, h11401, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h11385, h11397, h11400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h11385, h11396, h11399, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11408 | h11408
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11409 | h11409
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11410 | h11410
                      · linarith only [h11394, h11398, h11410, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11412 | h11412
                        · linarith only [h11394, h11398, h11408, h11412, hlam]
                        · rcases h1bigk with h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c | h11414c
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h0, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h0, h11393, h11409, h11412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            rcases p11414_3 (m.d 0 1) (by simp) with h11418 | h11418
                            · rcases p11414_3 (m.d 1 2) (by simp) with h11419 | h11419
                              · rcases p11414_3 (m.d 1 3) (by simp) with h11420 | h11420
                                · linarith only [h11385, h11420, hlam]
                                · linarith only [h11396, h11420, hlam]
                              · linarith only [h11394, h11419, hlam]
                            · linarith only [h11418, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            rcases p11414_3 (m.d 0 1) (by simp) with h11425 | h11425
                            · rcases p11414_3 (m.d 1 2) (by simp) with h11426 | h11426
                              · rcases p11414_3 (m.d 1 3) (by simp) with h11427 | h11427
                                · linarith only [h11385, h11427, hlam]
                                · linarith only [h11397, h11427, hlam]
                              · linarith only [h11395, h11426, hlam]
                            · linarith only [h11425, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11385, h11390, h11392, h11398, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            rcases p11414_3 (m.d 0 1) (by simp) with h11434 | h11434
                            · linarith only [h0, h11434, hlam]
                            · linarith only [h11385, h11434, hlam]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h0, h11385, h11390, h11392, h11398, hlam, p11414_2]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            rcases p11414_3 (m.d 0 1) (by simp) with h11438 | h11438
                            · linarith only [h0, h11438, hlam]
                            · linarith only [h11387, h11438, hlam]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11385, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11393, hlam, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h0, h11385, h11394, h11408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h0, h11385, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11386, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11394, hlam, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11396, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11398, hlam, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11387, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11395, hlam, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h11397, hlam, p11414_0]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [h0, h11387, h11394, h11408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11414_1]
                          · have p11414_0 := h11414c.1
                            have p11414_1 := h11414c.2.1
                            have p11414_2 := h11414c.2.2.1
                            have p11414_3 := h11414c.2.2.2
                            linarith only [hlam, p11414_0]
                    · linarith only [h0, h11385, h11397, h11409, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h11385, h11396, h11408, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h11385, h11391, h11396, h11397, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11459 | h11459
              · linarith only [h0, h11385, h11390, h11396, h11459, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11461 | h11461
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11462 | h11462
                  · linarith only [h11393, h11396, h11462, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11464 | h11464
                    · linarith only [h11393, h11459, h11464, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11466 | h11466
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11467 | h11467
                        · rcases h1bigk with h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c | h11468c
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h0, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            rcases p11468_3 (m.d 0 1) (by simp) with h11471 | h11471
                            · rcases p11468_3 (m.d 1 2) (by simp) with h11472 | h11472
                              · rcases p11468_3 (m.d 1 3) (by simp) with h11473 | h11473
                                · linarith only [h11473, hlam, p11468_0]
                                · rcases p11468_3 (m.d 1 4) (by simp) with h11475 | h11475
                                  · linarith only [h11386, h11475, hlam]
                                  · linarith only [h11396, h11475, hlam]
                              · linarith only [h11393, h11472, hlam]
                            · linarith only [h11471, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h0, h11394, h11466, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            rcases p11468_3 (m.d 0 1) (by simp) with h11481 | h11481
                            · rcases p11468_3 (m.d 1 2) (by simp) with h11482 | h11482
                              · rcases p11468_3 (m.d 1 3) (by simp) with h11483 | h11483
                                · linarith only [h11385, h11483, hlam]
                                · rcases p11468_3 (m.d 1 4) (by simp) with h11485 | h11485
                                  · linarith only [h11386, h11485, hlam]
                                  · linarith only [h11461, h11485, hlam]
                              · linarith only [h11395, h11482, hlam]
                            · linarith only [h11481, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11385, h11390, h11459, h11467, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h0, h11385, h11390, h11459, h11467, hlam, p11468_2]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            rcases p11468_3 (m.d 0 1) (by simp) with h11493 | h11493
                            · linarith only [h0, h11493, hlam]
                            · linarith only [h11386, h11493, hlam]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            rcases p11468_3 (m.d 0 1) (by simp) with h11496 | h11496
                            · linarith only [h0, h11496, hlam]
                            · linarith only [h11387, h11496, hlam]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11385, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11393, hlam, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11396, hlam, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11459, hlam, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11386, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11394, hlam, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h0, h11386, h11393, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h0, h11385, h11390, h11396, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11387, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11395, hlam, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h0, h11387, h11393, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11468_1]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [h11461, hlam, p11468_0]
                          · have p11468_0 := h11468c.1
                            have p11468_1 := h11468c.2.1
                            have p11468_2 := h11468c.2.2.1
                            have p11468_3 := h11468c.2.2.2
                            linarith only [hlam, p11468_0]
                        · linarith only [h11394, h11396, h11466, h11467, hlam]
                      · linarith only [h0, h11386, h11461, h11466, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11516 | h11516
                  · linarith only [h11393, h11396, h11516, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11518 | h11518
                    · linarith only [h0, h11385, h11390, h11392, h11393, h11396, h11461, h11518, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11520 | h11520
                      · linarith only [h11394, h11461, h11520, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11522 | h11522
                        · linarith only [h0, h11385, h11390, h11461, h11522, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h11385, h11390, h11392, h11393, h11396, h11522, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h11387, h11395, hlam]
        · linarith only [h0, h11389, h11394, hlam]
      · linarith only [h0, h11388, h11393, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11528 | h11528
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11529 | h11529
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11530 | h11530
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11531 | h11531
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11532 | h11532
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11533 | h11533
                · linarith only [h0, h11385, h11392, h11531, h11533, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11535 | h11535
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11536 | h11536
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11537 | h11537
                      · linarith only [h11386, h11392, h11529, h11537, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11539 | h11539
                        · linarith only [h0, h11385, h11392, h11528, h11535, h11539, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c | h11541c
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h0, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h0, h11528, h11536, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            rcases p11541_3 (m.d 0 1) (by simp) with h11545 | h11545
                            · rcases p11541_3 (m.d 1 2) (by simp) with h11546 | h11546
                              · rcases p11541_3 (m.d 1 3) (by simp) with h11547 | h11547
                                · linarith only [h11385, h11547, hlam]
                                · linarith only [h11531, h11547, hlam]
                              · linarith only [h11529, h11546, hlam]
                            · linarith only [h11545, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            rcases p11541_3 (m.d 0 1) (by simp) with h11552 | h11552
                            · rcases p11541_3 (m.d 1 2) (by simp) with h11553 | h11553
                              · rcases p11541_3 (m.d 1 3) (by simp) with h11554 | h11554
                                · linarith only [h11385, h11554, hlam]
                                · linarith only [h11532, h11554, hlam]
                              · linarith only [h11530, h11553, hlam]
                            · linarith only [h11552, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11385, h11528, h11536, h11539, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            rcases p11541_3 (m.d 0 1) (by simp) with h11561 | h11561
                            · linarith only [h0, h11561, hlam]
                            · linarith only [h11385, h11561, hlam]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            rcases p11541_3 (m.d 0 1) (by simp) with h11564 | h11564
                            · linarith only [h0, h11564, hlam]
                            · linarith only [h11386, h11564, hlam]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            rcases p11541_3 (m.d 0 1) (by simp) with h11567 | h11567
                            · linarith only [h0, h11567, hlam]
                            · linarith only [h11387, h11567, hlam]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11385, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11528, hlam, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h0, h11385, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h0, h11385, h11529, h11533, h11535, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11386, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11529, hlam, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11531, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11533, hlam, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11387, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11530, hlam, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h11532, hlam, p11541_0]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [h0, h11387, h11529, h11535, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11541_1]
                          · have p11541_0 := h11541c.1
                            have p11541_1 := h11541c.2.1
                            have p11541_2 := h11541c.2.2.1
                            have p11541_3 := h11541c.2.2.2
                            linarith only [hlam, p11541_0]
                    · linarith only [h0, h11385, h11532, h11536, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h11385, h11531, h11535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h11385, h11391, h11531, h11532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11588 | h11588
              · linarith only [h0, h11385, h11390, h11531, h11588, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11590 | h11590
                · linarith only [h0, h11386, h11392, h11590, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11592 | h11592
                  · linarith only [h11528, h11531, h11592, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11594 | h11594
                    · linarith only [h0, h11385, h11390, h11528, h11531, h11588, h11594, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11596 | h11596
                      · linarith only [h11389, h11390, h11392, h11528, h11531, h11596, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11598 | h11598
                        · linarith only [h11390, h11392, h11598, hlam]
                        · rcases h1bigk with h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c | h11600c
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h0, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            rcases p11600_3 (m.d 0 1) (by simp) with h11603 | h11603
                            · rcases p11600_3 (m.d 1 2) (by simp) with h11604 | h11604
                              · rcases p11600_3 (m.d 1 3) (by simp) with h11605 | h11605
                                · linarith only [h11605, hlam, p11600_0]
                                · rcases p11600_3 (m.d 1 4) (by simp) with h11607 | h11607
                                  · linarith only [h11386, h11607, hlam]
                                  · linarith only [h11531, h11607, hlam]
                              · linarith only [h11528, h11604, hlam]
                            · linarith only [h11603, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            rcases p11600_3 (m.d 0 1) (by simp) with h11612 | h11612
                            · rcases p11600_3 (m.d 1 2) (by simp) with h11613 | h11613
                              · rcases p11600_3 (m.d 1 3) (by simp) with h11614 | h11614
                                · linarith only [h11385, h11614, hlam]
                                · rcases p11600_3 (m.d 1 4) (by simp) with h11616 | h11616
                                  · linarith only [h11616, hlam, p11600_0]
                                  · rcases p11600_3 (m.d 1 5) (by simp) with h11618 | h11618
                                    · linarith only [h11387, h11618, hlam]
                                    · linarith only [h11590, h11618, hlam]
                              · linarith only [h11529, h11613, hlam]
                            · linarith only [h11612, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            rcases p11600_3 (m.d 0 1) (by simp) with h11623 | h11623
                            · rcases p11600_3 (m.d 1 2) (by simp) with h11624 | h11624
                              · rcases p11600_3 (m.d 1 3) (by simp) with h11625 | h11625
                                · linarith only [h11385, h11625, hlam]
                                · rcases p11600_3 (m.d 1 4) (by simp) with h11627 | h11627
                                  · linarith only [h11386, h11627, hlam]
                                  · rcases p11600_3 (m.d 1 5) (by simp) with h11629 | h11629
                                    · linarith only [h11629, hlam, p11600_0]
                                    · rcases h3bigk with h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c | h11631c
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11528, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11528, h11531, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11528, h11531, h11598, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11385, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11390, h11531, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11531, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11588, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11388, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11528, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11592, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11594, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11390, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11390, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11598, hlam, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h11391, hlam, p11631_0]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11391, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11391, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [h0, h11385, h11391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11631_1]
                                      · have p11631_0 := h11631c.1
                                        have p11631_1 := h11631c.2.1
                                        have p11631_2 := h11631c.2.2.1
                                        have p11631_3 := h11631c.2.2.2
                                        linarith only [hlam, p11631_0]
                              · linarith only [h11530, h11624, hlam]
                            · linarith only [h11623, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11385, h11390, h11528, h11531, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h0, h11385, h11390, h11531, hlam, p11600_2]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            rcases p11600_3 (m.d 0 1) (by simp) with h11662 | h11662
                            · linarith only [h0, h11662, hlam]
                            · linarith only [h11386, h11662, hlam]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            rcases p11600_3 (m.d 0 1) (by simp) with h11665 | h11665
                            · linarith only [h0, h11665, hlam]
                            · linarith only [h11387, h11665, hlam]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11385, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11528, hlam, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11531, hlam, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11588, hlam, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11386, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11529, hlam, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h0, h11386, h11528, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11590, hlam, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11387, hlam, p11600_0]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h11530, hlam, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h0, h11385, h11391, h11528, h11588, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [h0, h11385, h11391, h11588, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11600_1]
                          · have p11600_0 := h11600c.1
                            have p11600_1 := h11600c.2.1
                            have p11600_2 := h11600c.2.2.1
                            have p11600_3 := h11600c.2.2.2
                            linarith only [hlam, p11600_0]
          · linarith only [h0, h11387, h11530, hlam]
        · linarith only [h0, h11389, h11529, hlam]
      · linarith only [h0, h11388, h11528, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11686 | h11686
    · linarith only [h11390, h11391, h11686, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11688 | h11688
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11689 | h11689
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11690 | h11690
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11691 | h11691
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11692 | h11692
              · linarith only [h11385, h11391, h11692, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11694 | h11694
                · linarith only [h11386, h11686, h11694, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11696 | h11696
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11697 | h11697
                    · linarith only [h11385, h11391, h11688, h11697, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11699 | h11699
                      · linarith only [h11386, h11686, h11689, h11699, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11701 | h11701
                        · linarith only [h11387, h11686, h11688, h11692, h11696, h11701, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c | h11703c
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h0, hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h0, h11691, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            rcases p11703_3 (m.d 0 1) (by simp) with h11707 | h11707
                            · rcases p11703_3 (m.d 1 2) (by simp) with h11708 | h11708
                              · rcases p11703_3 (m.d 1 3) (by simp) with h11709 | h11709
                                · linarith only [h11385, h11709, hlam]
                                · linarith only [h11691, h11709, hlam]
                              · linarith only [h11689, h11708, hlam]
                            · linarith only [h11707, hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h0, h11690, h11696, h11697, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11385, h11688, h11696, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            rcases p11703_3 (m.d 0 1) (by simp) with h11717 | h11717
                            · linarith only [h0, h11717, hlam]
                            · linarith only [h11385, h11717, hlam]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            rcases p11703_3 (m.d 0 1) (by simp) with h11720 | h11720
                            · linarith only [h0, h11720, hlam]
                            · linarith only [h11386, h11720, hlam]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            rcases p11703_3 (m.d 0 1) (by simp) with h11723 | h11723
                            · linarith only [h0, h11723, hlam]
                            · linarith only [h11387, h11723, hlam]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11385, hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11688, hlam, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11385, h11391, h11701, hc14, hc45, hlam, hphi, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11692, hlam, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11386, hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11689, hlam, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11691, hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11694, hlam, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11387, hlam, p11703_0]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h11690, hlam, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h0, h11387, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [h0, h11387, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11703_1]
                          · have p11703_0 := h11703c.1
                            have p11703_1 := h11703c.2.1
                            have p11703_2 := h11703c.2.2.1
                            have p11703_3 := h11703c.2.2.2
                            linarith only [hlam, p11703_0]
                  · linarith only [h11390, h11391, h11696, hc23, hc35, hlam, hphi]
            · linarith only [h11390, h11391, h11688, h11691, hc23, hc35, hlam, hphi]
          · linarith only [h0, h11387, h11690, hlam]
        · linarith only [h0, h11389, h11689, hlam]
      · linarith only [h0, h11388, h11688, hlam]

end R2N4
