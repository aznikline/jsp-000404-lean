import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S6
import Jsp000404.R1LeavesN7_0S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11384000 in
set_option maxHeartbeats 11384000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  rcases m.htr 1 2 4 (by decide) (by decide) with h3576 | h3576
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3577 | h3577
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3578 | h3578
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3579 | h3579
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3580 | h3580
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3581 | h3581
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3582 | h3582
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3583 | h3583
                · linarith only [h0, h10, h3576, h3583, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h3576, h3580, h3583, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h3577, h3582, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h10, h3577, h3581, h7, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3588 | h3588
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3589 | h3589
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3590 | h3590
                · linarith only [h10, h3576, h3580, h3590, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3592 | h3592
                  · linarith only [h0, h10, h3576, h3580, h3588, h3592, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases h1bigk with h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c | h3594c
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      rcases p3594_3 (m.d 0 1) (by simp) with h3596 | h3596
                      · rcases p3594_3 (m.d 1 2) (by simp) with h3597 | h3597
                        · linarith only [h3597, hlam, p3594_0]
                        · rcases p3594_3 (m.d 1 3) (by simp) with h3599 | h3599
                          · linarith only [h1, h3599, hlam]
                          · linarith only [h10, h3599, hlam]
                      · linarith only [h3596, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      rcases p3594_3 (m.d 0 1) (by simp) with h3603 | h3603
                      · rcases p3594_3 (m.d 1 2) (by simp) with h3604 | h3604
                        · linarith only [h0, h3604, hlam]
                        · rcases p3594_3 (m.d 1 3) (by simp) with h3606 | h3606
                          · linarith only [h3606, hlam, p3594_0]
                          · rcases p3594_3 (m.d 1 4) (by simp) with h3608 | h3608
                            · linarith only [h2, h3608, hlam]
                            · rcases p3594_3 (m.d 1 5) (by simp) with h3610 | h3610
                              · linarith only [h3, h3610, hlam]
                              · rcases h1emax with h3612 | h3612 | h3612 | h3612 | h3612
                                · linarith only [h0, h10, h3612, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h2bigk with h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    rcases p3614_3 (m.d 0 2) (by simp) with h3616 | h3616
                                    · rcases p3614_3 (m.d 1 2) (by simp) with h3617 | h3617
                                      · linarith only [h0, h3617, hlam]
                                      · rcases p3614_3 (m.d 2 3) (by simp) with h3619 | h3619
                                        · linarith only [h3619, h4, hlam]
                                        · linarith only [h10, h3619, hlam]
                                    · linarith only [h0, h3616, hlam]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h0, h10, h3577, h3588, h3590, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3614_1]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h10, h3577, h3590, h4, hlam, p3614_2]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h10, h3577, h4, hlam, p3614_2]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h0, hlam, p3614_1]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h10, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h10, h3588, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3614_1]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h0, h10, h3588, h3590, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3614_1]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h4, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h0, h3576, h3588, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3614_1]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    rcases p3614_3 (m.d 0 2) (by simp) with h3634 | h3634
                                    · rcases p3614_3 (m.d 1 2) (by simp) with h3635 | h3635
                                      · linarith only [h10, h3635, hlam]
                                      · linarith only [h3576, h3635, hlam]
                                    · linarith only [h3634, h5, hlam]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    rcases p3614_3 (m.d 0 2) (by simp) with h3639 | h3639
                                    · rcases p3614_3 (m.d 1 2) (by simp) with h3640 | h3640
                                      · linarith only [h10, h3640, hlam]
                                      · linarith only [h3577, h3640, hlam]
                                    · linarith only [h3639, h6, hlam]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h5, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h3576, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h3588, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h3590, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h6, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h3577, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h3589, hlam, p3614_0]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [h0, h3577, h3588, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3614_1]
                                  · have p3614_0 := h3614c.1
                                    have p3614_1 := h3614c.2.1
                                    have p3614_2 := h3614c.2.2.1
                                    have p3614_3 := h3614c.2.2.2
                                    linarith only [hlam, p3614_0]
                                · rcases h2bigk with h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c | h3654c
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3656 | h3656
                                    · rcases p3654_3 (m.d 1 2) (by simp) with h3657 | h3657
                                      · linarith only [h0, h3657, hlam]
                                      · rcases p3654_3 (m.d 2 3) (by simp) with h3659 | h3659
                                        · linarith only [h3659, h4, hlam]
                                        · linarith only [h10, h3659, hlam]
                                    · linarith only [h0, h3656, hlam]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, h10, h3577, hc01, hc25, hlam, hphi, ht0b, ht5b, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3654_2]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h10, h3577, h4, hlam, p3654_2]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, hlam, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h10, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h10, h3612, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h10, h3612, hc25, hlam, hphi, ht01, ht0b, ht5b, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h4, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3576, h4, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3674 | h3674
                                    · rcases p3654_3 (m.d 1 2) (by simp) with h3675 | h3675
                                      · linarith only [h10, h3675, hlam]
                                      · linarith only [h3576, h3675, hlam]
                                    · linarith only [h3674, h5, hlam]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    rcases p3654_3 (m.d 0 2) (by simp) with h3679 | h3679
                                    · rcases p3654_3 (m.d 1 2) (by simp) with h3680 | h3680
                                      · linarith only [h10, h3680, hlam]
                                      · linarith only [h3577, h3680, hlam]
                                    · linarith only [h3679, h6, hlam]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h5, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3576, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3588, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3590, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h6, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3577, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h3589, hlam, p3654_0]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [h0, h3577, h3588, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3654_1]
                                  · have p3654_0 := h3654c.1
                                    have p3654_1 := h3654c.2.1
                                    have p3654_2 := h3654c.2.2.1
                                    have p3654_3 := h3654c.2.2.2
                                    linarith only [hlam, p3654_0]
                                · rcases h2bigk with h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c | h3694c
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    rcases p3694_3 (m.d 0 2) (by simp) with h3696 | h3696
                                    · rcases p3694_3 (m.d 1 2) (by simp) with h3697 | h3697
                                      · linarith only [h0, h3697, hlam]
                                      · rcases p3694_3 (m.d 2 3) (by simp) with h3699 | h3699
                                        · linarith only [h3699, h4, hlam]
                                        · linarith only [h10, h3699, hlam]
                                    · linarith only [h0, h3696, hlam]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h0, h10, h3577, hc01, hc25, hlam, hphi, ht0b, ht5b, p3694_1]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3694_2]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h10, h3577, h4, hlam, p3694_2]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h0, hlam, p3694_1]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h10, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3594_1, p3694_1]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p3594_1, p3694_1]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h4, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h0, h3576, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3694_1]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    rcases p3694_3 (m.d 0 2) (by simp) with h3714 | h3714
                                    · rcases p3694_3 (m.d 1 2) (by simp) with h3715 | h3715
                                      · linarith only [h10, h3715, hlam]
                                      · linarith only [h3576, h3715, hlam]
                                    · linarith only [h3714, h5, hlam]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    rcases p3694_3 (m.d 0 2) (by simp) with h3719 | h3719
                                    · rcases p3694_3 (m.d 1 2) (by simp) with h3720 | h3720
                                      · linarith only [h10, h3720, hlam]
                                      · linarith only [h3577, h3720, hlam]
                                    · linarith only [h3719, h6, hlam]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h5, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h3576, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h3588, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h3590, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h6, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h3577, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h3589, hlam, p3694_0]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [h0, h3577, h3588, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3694_1]
                                  · have p3694_0 := h3694c.1
                                    have p3694_1 := h3694c.2.1
                                    have p3694_2 := h3694c.2.2.1
                                    have p3694_3 := h3694c.2.2.2
                                    linarith only [hlam, p3694_0]
                                · rcases h2bigk with h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    rcases p3734_3 (m.d 0 2) (by simp) with h3736 | h3736
                                    · rcases p3734_3 (m.d 1 2) (by simp) with h3737 | h3737
                                      · linarith only [h0, h3737, hlam]
                                      · rcases p3734_3 (m.d 2 3) (by simp) with h3739 | h3739
                                        · linarith only [h3739, h4, hlam]
                                        · linarith only [h10, h3739, hlam]
                                    · linarith only [h0, h3736, hlam]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h0, h10, h3576, h3588, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3734_1]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3734_2]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h10, h3577, h4, hlam, p3734_2]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h0, hlam, p3734_1]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h10, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h0, h10, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3734_1]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h0, h10, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p3734_1]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h4, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h0, h3576, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3734_1]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    rcases p3734_3 (m.d 0 2) (by simp) with h3754 | h3754
                                    · rcases p3734_3 (m.d 1 2) (by simp) with h3755 | h3755
                                      · linarith only [h10, h3755, hlam]
                                      · linarith only [h3576, h3755, hlam]
                                    · linarith only [h3754, h5, hlam]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    rcases p3734_3 (m.d 0 2) (by simp) with h3759 | h3759
                                    · rcases p3734_3 (m.d 1 2) (by simp) with h3760 | h3760
                                      · linarith only [h10, h3760, hlam]
                                      · linarith only [h3577, h3760, hlam]
                                    · linarith only [h3759, h6, hlam]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h5, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h3576, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h3588, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h3590, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h6, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h3577, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h3589, hlam, p3734_0]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [h0, h3577, h3588, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3734_1]
                                  · have p3734_0 := h3734c.1
                                    have p3734_1 := h3734c.2.1
                                    have p3734_2 := h3734c.2.2.1
                                    have p3734_3 := h3734c.2.2.2
                                    linarith only [hlam, p3734_0]
                      · linarith only [h3603, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      rcases p3594_3 (m.d 0 1) (by simp) with h3775 | h3775
                      · rcases p3594_3 (m.d 1 2) (by simp) with h3776 | h3776
                        · linarith only [h0, h3776, hlam]
                        · linarith only [h3576, h3776, hlam]
                      · linarith only [h3775, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      rcases p3594_3 (m.d 0 1) (by simp) with h3780 | h3780
                      · rcases p3594_3 (m.d 1 2) (by simp) with h3781 | h3781
                        · linarith only [h0, h3781, hlam]
                        · linarith only [h3577, h3781, hlam]
                      · linarith only [h3780, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h0, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h10, hlam, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h0, h10, h3576, h3580, h3588, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h1, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h1, h3577, hc01, hc25, hlam, hphi, ht0b, ht5b, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      rcases p3594_3 (m.d 0 1) (by simp) with h3793 | h3793
                      · rcases p3594_3 (m.d 1 2) (by simp) with h3794 | h3794
                        · linarith only [h10, h3794, hlam]
                        · linarith only [h3576, h3794, hlam]
                      · linarith only [h2, h3793, hlam]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      rcases p3594_3 (m.d 0 1) (by simp) with h3798 | h3798
                      · rcases p3594_3 (m.d 1 2) (by simp) with h3799 | h3799
                        · linarith only [h10, h3799, hlam]
                        · linarith only [h3577, h3799, hlam]
                      · linarith only [h3, h3798, hlam]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h2, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h3576, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h3578, hlam, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h3580, hlam, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h3, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h3577, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h3579, hlam, p3594_0]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [h0, h10, h3576, h3577, h3588, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3594_1]
                    · have p3594_0 := h3594c.1
                      have p3594_1 := h3594c.2.1
                      have p3594_2 := h3594c.2.2.1
                      have p3594_3 := h3594c.2.2.2
                      linarith only [hlam, p3594_0]
              · linarith only [h0, h10, h3576, h3588, h3589, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h3576, h3588, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h10, h3577, h3579, hlam]
      · linarith only [h10, h3576, h3578, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3817 | h3817
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3818 | h3818
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3819 | h3819
          · linarith only [h3576, h3577, h3819, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3821 | h3821
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3822 | h3822
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3823 | h3823
                · linarith only [h3576, h3577, h3819, h3822, h3823, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3825 | h3825
                  · linarith only [h3576, h3577, h3821, h3823, h3825, hlam]
                  · rcases h1bigk with h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c | h3827c
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      rcases p3827_3 (m.d 0 1) (by simp) with h3829 | h3829
                      · rcases p3827_3 (m.d 1 2) (by simp) with h3830 | h3830
                        · linarith only [h3830, hlam, p3827_0]
                        · rcases p3827_3 (m.d 1 3) (by simp) with h3832 | h3832
                          · linarith only [h1, h3832, hlam]
                          · linarith only [h10, h3832, hlam]
                      · linarith only [h3829, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      rcases p3827_3 (m.d 0 1) (by simp) with h3836 | h3836
                      · rcases p3827_3 (m.d 1 2) (by simp) with h3837 | h3837
                        · linarith only [h0, h3837, hlam]
                        · rcases p3827_3 (m.d 1 3) (by simp) with h3839 | h3839
                          · linarith only [h3839, hlam, p3827_0]
                          · rcases p3827_3 (m.d 1 4) (by simp) with h3841 | h3841
                            · linarith only [h2, h3841, hlam]
                            · rcases p3827_3 (m.d 1 5) (by simp) with h3843 | h3843
                              · linarith only [h3, h3843, hlam]
                              · rcases h1emax with h3845 | h3845 | h3845 | h3845 | h3845
                                · linarith only [h0, h3577, h3823, h3845, h4, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h2bigk with h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c | h3847c
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    rcases p3847_3 (m.d 0 2) (by simp) with h3849 | h3849
                                    · rcases p3847_3 (m.d 1 2) (by simp) with h3850 | h3850
                                      · linarith only [h0, h3850, hlam]
                                      · rcases p3847_3 (m.d 2 3) (by simp) with h3852 | h3852
                                        · linarith only [h3852, h4, hlam]
                                        · linarith only [h10, h3852, hlam]
                                    · linarith only [h0, h3849, hlam]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h0, h10, h3576, h3821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3847_2]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3576, h3577, h3821, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h0, hlam, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h10, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3577, h3821, h3823, h7, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3577, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h4, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h0, h3576, h3821, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    rcases p3847_3 (m.d 0 2) (by simp) with h3867 | h3867
                                    · rcases p3847_3 (m.d 1 2) (by simp) with h3868 | h3868
                                      · linarith only [h10, h3868, hlam]
                                      · linarith only [h3576, h3868, hlam]
                                    · linarith only [h3867, h5, hlam]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h0, h3576, h3577, h3821, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h5, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3576, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3821, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3823, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h6, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h0, h3576, h3821, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3847_1]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [h3822, hlam, p3847_0]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    rcases p3847_3 (m.d 0 2) (by simp) with h3881 | h3881
                                    · rcases p3847_3 (m.d 1 2) (by simp) with h3882 | h3882
                                      · linarith only [h3577, h3882, hlam]
                                      · linarith only [h3576, h3882, hlam]
                                    · linarith only [h3881, h5, hlam]
                                  · have p3847_0 := h3847c.1
                                    have p3847_1 := h3847c.2.1
                                    have p3847_2 := h3847c.2.2.1
                                    have p3847_3 := h3847c.2.2.2
                                    linarith only [hlam, p3847_0]
                                · rcases h2bigk with h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    rcases p3887_3 (m.d 0 2) (by simp) with h3889 | h3889
                                    · rcases p3887_3 (m.d 1 2) (by simp) with h3890 | h3890
                                      · linarith only [h0, h3890, hlam]
                                      · rcases p3887_3 (m.d 2 3) (by simp) with h3892 | h3892
                                        · linarith only [h3892, h4, hlam]
                                        · linarith only [h10, h3892, hlam]
                                    · linarith only [h0, h3889, hlam]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h10, h3576, h3821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3887_2]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3576, h3577, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, hlam, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h10, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3577, h3818, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3827_1, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3577, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h4, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3576, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    rcases p3887_3 (m.d 0 2) (by simp) with h3907 | h3907
                                    · rcases p3887_3 (m.d 1 2) (by simp) with h3908 | h3908
                                      · linarith only [h10, h3908, hlam]
                                      · linarith only [h3576, h3908, hlam]
                                    · linarith only [h3907, h5, hlam]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3576, h3577, h3821, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h5, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3576, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3821, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3823, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h6, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3576, h3821, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3822, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    rcases p3887_3 (m.d 0 2) (by simp) with h3921 | h3921
                                    · rcases p3887_3 (m.d 1 2) (by simp) with h3922 | h3922
                                      · linarith only [h3577, h3922, hlam]
                                      · linarith only [h3576, h3922, hlam]
                                    · linarith only [h3921, h5, hlam]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                · rcases h2bigk with h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    rcases p3927_3 (m.d 0 2) (by simp) with h3929 | h3929
                                    · rcases p3927_3 (m.d 1 2) (by simp) with h3930 | h3930
                                      · linarith only [h0, h3930, hlam]
                                      · rcases p3927_3 (m.d 2 3) (by simp) with h3932 | h3932
                                        · linarith only [h3932, h4, hlam]
                                        · linarith only [h10, h3932, hlam]
                                    · linarith only [h0, h3929, hlam]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h0, h10, h3576, h3821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3927_2]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h0, h3576, h3577, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h0, hlam, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h10, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3827_1, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h3577, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h4, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h0, h3576, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    rcases p3927_3 (m.d 0 2) (by simp) with h3947 | h3947
                                    · rcases p3927_3 (m.d 1 2) (by simp) with h3948 | h3948
                                      · linarith only [h10, h3948, hlam]
                                      · linarith only [h3576, h3948, hlam]
                                    · linarith only [h3947, h5, hlam]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h0, h3576, h3577, h3821, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h5, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h3576, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h3821, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h3823, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h6, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h3576, h3821, h3823, hc34, hc45, hlam, hphi, p3927_1]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [h3822, hlam, p3927_0]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    rcases p3927_3 (m.d 0 2) (by simp) with h3961 | h3961
                                    · rcases p3927_3 (m.d 1 2) (by simp) with h3962 | h3962
                                      · linarith only [h3577, h3962, hlam]
                                      · linarith only [h3576, h3962, hlam]
                                    · linarith only [h3961, h5, hlam]
                                  · have p3927_0 := h3927c.1
                                    have p3927_1 := h3927c.2.1
                                    have p3927_2 := h3927c.2.2.1
                                    have p3927_3 := h3927c.2.2.2
                                    linarith only [hlam, p3927_0]
                                · rcases h2bigk with h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c | h3967c
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    rcases p3967_3 (m.d 0 2) (by simp) with h3969 | h3969
                                    · rcases p3967_3 (m.d 1 2) (by simp) with h3970 | h3970
                                      · linarith only [h0, h3970, hlam]
                                      · rcases p3967_3 (m.d 2 3) (by simp) with h3972 | h3972
                                        · linarith only [h3972, h4, hlam]
                                        · linarith only [h10, h3972, hlam]
                                    · linarith only [h0, h3969, hlam]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, h10, h3576, h3821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h10, h3576, h4, hlam, p3967_2]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, h3576, h3577, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, hlam, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h10, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, h3577, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h3577, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h4, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, h3576, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    rcases p3967_3 (m.d 0 2) (by simp) with h3987 | h3987
                                    · rcases p3967_3 (m.d 1 2) (by simp) with h3988 | h3988
                                      · linarith only [h10, h3988, hlam]
                                      · linarith only [h3576, h3988, hlam]
                                    · linarith only [h3987, h5, hlam]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, h3576, h3577, h3821, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h5, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h3576, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h3821, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h3823, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h6, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h0, h3576, h3821, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3967_1]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [h3822, hlam, p3967_0]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    rcases p3967_3 (m.d 0 2) (by simp) with h4001 | h4001
                                    · rcases p3967_3 (m.d 1 2) (by simp) with h4002 | h4002
                                      · linarith only [h3577, h4002, hlam]
                                      · linarith only [h3576, h4002, hlam]
                                    · linarith only [h4001, h5, hlam]
                                  · have p3967_0 := h3967c.1
                                    have p3967_1 := h3967c.2.1
                                    have p3967_2 := h3967c.2.2.1
                                    have p3967_3 := h3967c.2.2.2
                                    linarith only [hlam, p3967_0]
                      · linarith only [h3836, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      rcases p3827_3 (m.d 0 1) (by simp) with h4008 | h4008
                      · rcases p3827_3 (m.d 1 2) (by simp) with h4009 | h4009
                        · linarith only [h0, h4009, hlam]
                        · linarith only [h3576, h4009, hlam]
                      · linarith only [h4008, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      rcases p3827_3 (m.d 0 1) (by simp) with h4013 | h4013
                      · rcases p3827_3 (m.d 1 2) (by simp) with h4014 | h4014
                        · linarith only [h0, h4014, hlam]
                        · rcases p3827_3 (m.d 1 3) (by simp) with h4016 | h4016
                          · linarith only [h1, h4016, hlam]
                          · linarith only [h3818, h4016, hlam]
                      · linarith only [h4013, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h0, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h10, hlam, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3577, hlam, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h1, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h1, h3576, h3821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      rcases p3827_3 (m.d 0 1) (by simp) with h4028 | h4028
                      · rcases p3827_3 (m.d 1 2) (by simp) with h4029 | h4029
                        · linarith only [h10, h4029, hlam]
                        · linarith only [h3576, h4029, hlam]
                      · linarith only [h2, h4028, hlam]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h0, h10, h3576, h3577, h3821, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h2, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3576, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3817, hlam, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3819, hlam, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3, h3576, h3821, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3827_1]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [h3818, hlam, p3827_0]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      rcases p3827_3 (m.d 0 1) (by simp) with h4042 | h4042
                      · rcases p3827_3 (m.d 1 2) (by simp) with h4043 | h4043
                        · linarith only [h3577, h4043, hlam]
                        · linarith only [h3576, h4043, hlam]
                      · linarith only [h2, h4042, hlam]
                    · have p3827_0 := h3827c.1
                      have p3827_1 := h3827c.2.1
                      have p3827_2 := h3827c.2.2.1
                      have p3827_3 := h3827c.2.2.2
                      linarith only [hlam, p3827_0]
              · linarith only [h0, h10, h3576, h3821, h3822, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h3576, h3821, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4050 | h4050
          · linarith only [h3576, h3577, h4050, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4052 | h4052
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4053 | h4053
              · linarith only [h0, h10, h3576, h3818, h4, h4053, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h3576, h4, h4052, h4053, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h3576, h4, h4052, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h3576, h3817, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s14 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h3576

set_option maxHeartbeats 18516000 in
set_option maxHeartbeats 18516000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s10 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s13 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

end R2N4
