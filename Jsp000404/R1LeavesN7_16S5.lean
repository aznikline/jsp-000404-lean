import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3093 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3422 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3423 | h3423
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3424 | h3424
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3425 | h3425
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3426 | h3426
        · linarith only [h0, h3426, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3428 | h3428
          · linarith only [h0, h3093, h3428, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3430 | h3430
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3431 | h3431
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3432 | h3432
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3433 | h3433
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3434 | h3434
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3435 | h3435
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3436 | h3436
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3437 | h3437
                          · rcases h1bigk with h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c | h3438c
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3430, h3435, h3437, hc01, hc45, hlam, hphi, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3431, h3437, hc01, hc45, hlam, hphi, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3428, h3430, h3435, h3437, hc01, hc45, hlam, hphi, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              rcases p3438_3 (m.d 0 1) (by simp) with h3443 | h3443
                              · rcases p3438_3 (m.d 1 2) (by simp) with h3444 | h3444
                                · linarith only [h0, h3444, hlam]
                                · linarith only [h3430, h3444, hlam]
                              · linarith only [h3443, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h0, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3426, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3428, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h0, h3093, h3434, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h1, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h1, h3428, h3430, h3435, hc01, hc35, hlam, hphi, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h1, h3430, h3435, hc01, hc35, hlam, hphi, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h2, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3430, h3435, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3431, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h2, h3430, h3435, hc01, hc35, hlam, hphi, ht0b, ht5b, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3430, hlam, p3438_1]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3432, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [h3433, hlam, p3438_0]
                            · have p3438_0 := h3438c.1
                              have p3438_1 := h3438c.2.1
                              have p3438_2 := h3438c.2.2.1
                              have p3438_3 := h3438c.2.2.2
                              linarith only [hlam, p3438_0]
                          · rcases h1bigk with h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3430, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3426, h3430, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3428, h3430, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3430, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h0, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3426, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3428, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h0, h3093, h3430, h3434, h3436, h3437, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h1, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h1, h3428, h3430, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h1, h3430, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h2, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3430, h3436, h3437, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3431, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h1, h3430, h3431, h3436, h3437, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3430, hlam, p3468_1]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3432, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [h3433, hlam, p3468_0]
                            · have p3468_0 := h3468c.1
                              have p3468_1 := h3468c.2.1
                              have p3468_2 := h3468c.2.2.1
                              have p3468_3 := h3468c.2.2.2
                              linarith only [hlam, p3468_0]
                        · linarith only [h3093, h3425, h3436, hlam]
                      · linarith only [h3424, h3435, h4, hlam]
                    · linarith only [h3423, h3434, h4, hlam]
                  · linarith only [h3428, h3430, h3433, hlam]
                · linarith only [h3428, h3430, h3431, h3432, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3499 | h3499
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3500 | h3500
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3501 | h3501
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3502 | h3502
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3503 | h3503
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3504 | h3504
                          · rcases h1bigk with h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c | h3505c
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3430, hc01, hc25, hlam, hphi, ht0b, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3426, h3430, h3502, h3504, hc01, hc45, hlam, hphi, ht0b, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3426, h3430, h3431, h3502, h3504, hc01, hc45, hlam, hphi, ht0b, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              rcases p3505_3 (m.d 0 1) (by simp) with h3510 | h3510
                              · rcases p3505_3 (m.d 1 2) (by simp) with h3511 | h3511
                                · linarith only [h0, h3511, hlam]
                                · linarith only [h3430, h3511, hlam]
                              · linarith only [h3510, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h0, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3426, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3428, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3423, h3426, h3430, h3431, h3502, h3504, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h1, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3423, h3431, h4, hc12, hc23, hlam, hphi, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3431, hlam, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3423, h3430, h3431, h3502, h3504, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h2, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3430, h3502, h3504, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3423, h3431, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3423, h3430, h3431, h3502, h3504, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3430, hlam, p3505_1]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3499, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [h3500, hlam, p3505_0]
                            · have p3505_0 := h3505c.1
                              have p3505_1 := h3505c.2.1
                              have p3505_2 := h3505c.2.2.1
                              have p3505_3 := h3505c.2.2.2
                              linarith only [hlam, p3505_0]
                          · linarith only [h3425, h3426, h3430, h3431, h3502, h3504, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h3093, h3425, h3503, hlam]
                      · linarith only [h3423, h3426, h3431, h3502, h4, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h3423, h3501, h4, hlam]
                  · linarith only [h3426, h3430, h3431, h3500, hlam]
                · linarith only [h3426, h3430, h3499, hlam]
            · linarith only [h3093, h3422, h3430, hc12, hc24, hlam, hphi]
      · linarith only [h3093, h3422, h3425, hlam]
    · linarith only [h3093, h3422, h3423, h3424, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3544 | h3544
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3545 | h3545
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3546 | h3546
        · linarith only [h0, h3422, h3546, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3548 | h3548
          · linarith only [h0, h3093, h3548, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3550 | h3550
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3551 | h3551
              · linarith only [h0, h1, h3423, h3550, h3551, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3553 | h3553
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3554 | h3554
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3555 | h3555
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3556 | h3556
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3557 | h3557
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3558 | h3558
                          · rcases h1bigk with h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c | h3559c
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3550, h3556, h3558, hc01, hc45, hlam, hphi, ht0b, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3546, h3550, h3556, h3558, hc01, hc45, hlam, hphi, ht0b, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3546, h3550, h3551, h3556, h3558, hc01, hc45, hlam, hphi, ht0b, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              rcases p3559_3 (m.d 0 1) (by simp) with h3564 | h3564
                              · rcases p3559_3 (m.d 1 2) (by simp) with h3565 | h3565
                                · linarith only [h0, h3565, hlam]
                                · linarith only [h3550, h3565, hlam]
                              · linarith only [h3564, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h0, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3546, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3548, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h0, h3423, h3555, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h1, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3550, h3551, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3551, hlam, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h1, h3550, h3556, h3558, hc01, hc45, hlam, hphi, ht0b, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h2, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h2, h3423, h3550, h3555, h3556, h3558, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h2, h3423, h3555, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h2, h3423, h3550, h3555, h3556, h3558, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3550, hlam, p3559_1]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3553, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [h3554, hlam, p3559_0]
                            · have p3559_0 := h3559c.1
                              have p3559_1 := h3559c.2.1
                              have p3559_2 := h3559c.2.2.1
                              have p3559_3 := h3559c.2.2.2
                              linarith only [hlam, p3559_0]
                          · linarith only [h3423, h3545, h3558, hlam]
                        · linarith only [h1, h3, h3423, h3546, h3550, h3554, h3555, h3557, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h3423, h3544, h3556, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3592 | h3592
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3593 | h3593
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3594 | h3594
                          · rcases h1bigk with h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c | h3595c
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3550, hc01, hc25, hlam, hphi, ht0b, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3546, h3550, h3592, h3594, hc01, hc45, hlam, hphi, ht0b, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3548, h3550, h3592, h3594, hc01, hc45, hlam, hphi, ht0b, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              rcases p3595_3 (m.d 0 1) (by simp) with h3600 | h3600
                              · rcases p3595_3 (m.d 1 2) (by simp) with h3601 | h3601
                                · linarith only [h0, h3601, hlam]
                                · linarith only [h3550, h3601, hlam]
                              · linarith only [h3600, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h0, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3546, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3548, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h0, h3555, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h1, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3550, h3551, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3551, hlam, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h1, h3550, h3555, h3592, h3594, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h2, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h2, h3550, h3592, h3594, hc01, hc45, hlam, hphi, ht0b, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h2, h3550, h3592, h3594, hc01, hc45, hlam, hphi, ht0b, ht5b, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3550, hlam, p3595_1]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3553, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [h3554, hlam, p3595_0]
                            · have p3595_0 := h3595c.1
                              have p3595_1 := h3595c.2.1
                              have p3595_2 := h3595c.2.2.1
                              have p3595_3 := h3595c.2.2.2
                              linarith only [hlam, p3595_0]
                          · linarith only [h0, h3550, h3555, h3592, h3594, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h3093, h3545, h3593, hlam]
                      · linarith only [h3544, h3592, h4, hlam]
                  · linarith only [h3546, h3550, h3551, h3554, hlam]
                · linarith only [h3423, h3544, h3546, h3550, h3553, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h3422, h3550, h4, hc12, hc23, hlam, hphi]
      · linarith only [h3422, h3423, h3545, h4, hlam]
    · linarith only [h3422, h3544, h4, hlam]

end R2N4
