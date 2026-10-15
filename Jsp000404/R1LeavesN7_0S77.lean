import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S76

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8488000 in
set_option maxHeartbeats 8488000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h41030 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h44266 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  rcases m.htr 0 4 5 (by decide) (by decide) with h44509 | h44509
  · rcases m.htr 1 2 3 (by decide) (by decide) with h44510 | h44510
    · rcases m.htr 1 2 4 (by decide) (by decide) with h44511 | h44511
      · rcases m.htr 1 2 5 (by decide) (by decide) with h44512 | h44512
        · rcases m.htr 1 3 4 (by decide) (by decide) with h44513 | h44513
          · rcases m.htr 1 3 5 (by decide) (by decide) with h44514 | h44514
            · rcases m.htr 1 4 5 (by decide) (by decide) with h44515 | h44515
              · rcases m.htr 2 3 4 (by decide) (by decide) with h44516 | h44516
                · linarith only [h41027, h41030, h44516, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h44518 | h44518
                  · linarith only [h41027, h44266, h44518, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h44520 | h44520
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h44521 | h44521
                      · rcases h1bigk with h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c | h44522c
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h0, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h36828, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h39227, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          rcases p44522_3 (m.d 0 1) (by simp) with h44528 | h44528
                          · linarith only [h44528, hlam, p44522_0]
                          · rcases p44522_3 (m.d 1 2) (by simp) with h44530 | h44530
                            · rcases p44522_3 (m.d 1 3) (by simp) with h44531 | h44531
                              · linarith only [h44510, h44531, hlam]
                              · linarith only [h33187, h44531, hlam]
                            · linarith only [h44530, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, h44266, h44513, h44521, hc01, hc12, hlam, hphi, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, h44266, h44514, h44515, hc01, hc12, hlam, hphi, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, h44266, h44514, hc01, hc12, hlam, hphi, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          rcases p44522_3 (m.d 0 1) (by simp) with h44539 | h44539
                          · linarith only [h44539, hlam, p44522_0]
                          · rcases p44522_3 (m.d 1 2) (by simp) with h44541 | h44541
                            · rcases p44522_3 (m.d 1 3) (by simp) with h44542 | h44542
                              · rcases p44522_3 (m.d 1 4) (by simp) with h44543 | h44543
                                · linarith only [h44513, h44543, hlam]
                                · linarith only [h36828, h44543, hlam]
                              · linarith only [h44542, hlam, p44522_0]
                            · linarith only [h0, h44541, hlam]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h44510, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, h44266, h44514, h44515, hc01, hc13, hlam, hphi, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, h44266, h44510, h44514, hc01, hc12, hlam, hphi, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          rcases p44522_3 (m.d 0 1) (by simp) with h44552 | h44552
                          · linarith only [h44552, hlam, p44522_0]
                          · rcases p44522_3 (m.d 1 2) (by simp) with h44554 | h44554
                            · rcases p44522_3 (m.d 1 3) (by simp) with h44555 | h44555
                              · rcases p44522_3 (m.d 1 4) (by simp) with h44556 | h44556
                                · rcases p44522_3 (m.d 1 5) (by simp) with h44557 | h44557
                                  · linarith only [h44515, h44557, hlam]
                                  · linarith only [h39227, h44557, hlam]
                                · linarith only [h44556, hlam, p44522_0]
                              · linarith only [h33187, h44555, hlam]
                            · linarith only [h0, h44554, hlam]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h44511, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h44513, hlam, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h33187, h44266, h44514, hc01, hc14, hlam, hphi, p44522_1]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          rcases p44522_3 (m.d 0 1) (by simp) with h44567 | h44567
                          · linarith only [h44567, hlam, p44522_0]
                          · rcases p44522_3 (m.d 1 2) (by simp) with h44569 | h44569
                            · rcases p44522_3 (m.d 1 3) (by simp) with h44570 | h44570
                              · rcases p44522_3 (m.d 1 4) (by simp) with h44571 | h44571
                                · rcases p44522_3 (m.d 1 5) (by simp) with h44572 | h44572
                                  · rcases h1emax with h44573 | h44573 | h44573 | h44573 | h44573
                                    · rcases h2bigk with h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c | h44574c
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h0, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44577 | h44577
                                        · rcases p44574_3 (m.d 1 2) (by simp) with h44578 | h44578
                                          · rcases p44574_3 (m.d 2 3) (by simp) with h44579 | h44579
                                            · linarith only [h44579, hlam, p44574_0]
                                            · rcases p44574_3 (m.d 2 4) (by simp) with h44581 | h44581
                                              · linarith only [h41028, h44581, hlam]
                                              · linarith only [h44516, h44581, hlam]
                                          · linarith only [h44510, h44578, hlam]
                                        · linarith only [h44577, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44586 | h44586
                                        · rcases p44574_3 (m.d 1 2) (by simp) with h44587 | h44587
                                          · rcases p44574_3 (m.d 2 3) (by simp) with h44588 | h44588
                                            · linarith only [h41027, h44588, hlam]
                                            · rcases p44574_3 (m.d 2 4) (by simp) with h44590 | h44590
                                              · linarith only [h44590, hlam, p44574_0]
                                              · rcases p44574_3 (m.d 2 5) (by simp) with h44592 | h44592
                                                · linarith only [h41029, h44592, hlam]
                                                · rcases h4bigk with h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c | h44594c
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h36828, hlam, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h41030, h44510, h44513, h44520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h41030, hlam, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    rcases p44594_3 (m.d 0 4) (by simp) with h44599 | h44599
                                                    · rcases p44594_3 (m.d 1 4) (by simp) with h44600 | h44600
                                                      · rcases p44594_3 (m.d 2 4) (by simp) with h44601 | h44601
                                                        · linarith only [h41028, h44601, hlam]
                                                        · linarith only [h44520, h44601, hlam]
                                                      · linarith only [h44515, h44600, hlam]
                                                    · linarith only [h44599, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    rcases p44594_3 (m.d 0 4) (by simp) with h44606 | h44606
                                                    · linarith only [h36828, h44606, hlam]
                                                    · rcases p44594_3 (m.d 1 4) (by simp) with h44608 | h44608
                                                      · rcases p44594_3 (m.d 2 4) (by simp) with h44609 | h44609
                                                        · linarith only [h44511, h44609, hlam]
                                                        · rcases p44594_3 (m.d 3 4) (by simp) with h44611 | h44611
                                                          · linarith only [h44513, h44611, hlam]
                                                          · linarith only [h41030, h44611, hlam]
                                                      · linarith only [h36828, h44608, hlam]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    rcases p44594_3 (m.d 0 4) (by simp) with h44616 | h44616
                                                    · linarith only [h36828, h44616, hlam]
                                                    · linarith only [h41028, h44616, hlam]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h33187, h41030, h44510, h44513, hc01, hc12, hlam, hphi, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    rcases p44594_3 (m.d 0 4) (by simp) with h44620 | h44620
                                                    · linarith only [h36828, h44620, hlam]
                                                    · linarith only [h44509, h44620, hlam]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h41028, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44511, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44516, hlam, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p44574_1, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h36828, h44510, h44513, hc01, hc12, hlam, hphi, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44513, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44510, h44513, h44520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44594_1]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    rcases p44594_3 (m.d 0 4) (by simp) with h44632 | h44632
                                                    · linarith only [h41030, h44632, hlam]
                                                    · linarith only [h44509, h44632, hlam]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44509, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44515, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44520, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [h44521, hlam, p44594_0]
                                                  · have p44594_0 := h44594c.1
                                                    have p44594_1 := h44594c.2.1
                                                    have p44594_2 := h44594c.2.2.1
                                                    have p44594_3 := h44594c.2.2.2
                                                    linarith only [hlam, p44594_0]
                                          · linarith only [h44511, h44587, hlam]
                                        · linarith only [h44586, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44642 | h44642
                                        · rcases p44574_3 (m.d 1 2) (by simp) with h44643 | h44643
                                          · rcases p44574_3 (m.d 2 3) (by simp) with h44644 | h44644
                                            · linarith only [h41027, h44644, hlam]
                                            · rcases p44574_3 (m.d 2 4) (by simp) with h44646 | h44646
                                              · linarith only [h41028, h44646, hlam]
                                              · linarith only [h44520, h44646, hlam]
                                          · linarith only [h44512, h44643, hlam]
                                        · linarith only [h44642, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h41028, h44520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44574_1]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44653 | h44653
                                        · linarith only [h0, h44653, hlam]
                                        · linarith only [h41027, h44653, hlam]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44656 | h44656
                                        · linarith only [h0, h44656, hlam]
                                        · linarith only [h41028, h44656, hlam]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44659 | h44659
                                        · linarith only [h0, h44659, hlam]
                                        · linarith only [h41029, h44659, hlam]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h41027, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h44510, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h44516, hlam, p44574_1]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h44518, hlam, p44574_1]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h41028, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h44511, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44669 | h44669
                                        · rcases p44574_3 (m.d 1 2) (by simp) with h44670 | h44670
                                          · rcases p44574_3 (m.d 2 3) (by simp) with h44671 | h44671
                                            · linarith only [h44516, h44671, hlam]
                                            · rcases p44574_3 (m.d 2 4) (by simp) with h44673 | h44673
                                              · rcases p44574_3 (m.d 2 5) (by simp) with h44674 | h44674
                                                · linarith only [h44520, h44674, hlam]
                                                · linarith only [h44518, h44674, hlam]
                                              · linarith only [h44516, h44673, hlam]
                                          · linarith only [h44510, h44670, hlam]
                                        · linarith only [h41027, h44669, hlam]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44681 | h44681
                                        · rcases p44574_3 (m.d 1 2) (by simp) with h44682 | h44682
                                          · rcases p44574_3 (m.d 2 3) (by simp) with h44683 | h44683
                                            · linarith only [h44516, h44683, hlam]
                                            · rcases p44574_3 (m.d 2 4) (by simp) with h44685 | h44685
                                              · rcases p44574_3 (m.d 2 5) (by simp) with h44686 | h44686
                                                · linarith only [h44520, h44686, hlam]
                                                · rcases h4bigk with h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c | h44688c
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h36828, hlam, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44518, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44574_1, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h41030, hlam, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    rcases p44688_3 (m.d 0 4) (by simp) with h44693 | h44693
                                                    · rcases p44688_3 (m.d 1 4) (by simp) with h44694 | h44694
                                                      · rcases p44688_3 (m.d 2 4) (by simp) with h44695 | h44695
                                                        · linarith only [h41028, h44695, hlam]
                                                        · linarith only [h44520, h44695, hlam]
                                                      · linarith only [h44515, h44694, hlam]
                                                    · linarith only [h44693, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h41028, h44518, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44511, h44518, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h33187, h41030, h44510, h44513, hc01, hc12, hlam, hphi, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    rcases p44688_3 (m.d 0 4) (by simp) with h44704 | h44704
                                                    · linarith only [h36828, h44704, hlam]
                                                    · linarith only [h44509, h44704, hlam]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h41028, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44511, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44516, hlam, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    rcases p44688_3 (m.d 0 4) (by simp) with h44711 | h44711
                                                    · rcases p44688_3 (m.d 1 4) (by simp) with h44712 | h44712
                                                      · rcases p44688_3 (m.d 2 4) (by simp) with h44713 | h44713
                                                        · rcases p44688_3 (m.d 3 4) (by simp) with h44714 | h44714
                                                          · rcases p44688_3 (m.d 4 5) (by simp) with h44715 | h44715
                                                            · linarith only [h44715, hlam, p44688_0]
                                                            · rcases h5bigk with h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c | h44717c
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [hlam, p44717_0]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h39227, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44266, h44518, hc23, hc35, hlam, hphi, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44266, hlam, p44717_0]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h41030, h44509, h44510, h44513, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h39227, hc01, hc15, hlam, hphi, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [hlam, p44717_0]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                rcases p44717_3 (m.d 0 5) (by simp) with h44725 | h44725
                                                                · linarith only [h39227, h44725, hlam]
                                                                · linarith only [h41029, h44725, hlam]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h33187, h44266, h44515, hc01, hc14, hlam, hphi, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                rcases p44717_3 (m.d 0 5) (by simp) with h44729 | h44729
                                                                · linarith only [h39227, h44729, hlam]
                                                                · linarith only [h44509, h44729, hlam]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h41029, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44512, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [hlam, p44717_0]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44518, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h41028, hc02, hc45, hlam, hphi, ht0b, ht5b, p44574_1, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h33187, h44266, hc01, hc35, hlam, hphi, ht12, ht23, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44514, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44510, h44514, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [hlam, p44717_0]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44510, h44513, h44521, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44509, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44515, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44520, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [h44521, hlam, p44717_1]
                                                              · have p44717_0 := h44717c.1
                                                                have p44717_1 := h44717c.2.1
                                                                have p44717_2 := h44717c.2.2.1
                                                                have p44717_3 := h44717c.2.2.2
                                                                linarith only [hlam, p44717_0]
                                                          · linarith only [h44521, h44714, hlam]
                                                        · linarith only [h44713, hlam, p44688_0]
                                                      · linarith only [h44515, h44712, hlam]
                                                    · linarith only [h44509, h44711, hlam]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h41028, h44510, h44513, h44518, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44513, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44510, h44513, h44518, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44688_1]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    rcases p44688_3 (m.d 0 4) (by simp) with h44755 | h44755
                                                    · linarith only [h41030, h44755, hlam]
                                                    · linarith only [h44509, h44755, hlam]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44509, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44515, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44520, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [h44521, hlam, p44688_0]
                                                  · have p44688_0 := h44688c.1
                                                    have p44688_1 := h44688c.2.1
                                                    have p44688_2 := h44688c.2.2.1
                                                    have p44688_3 := h44688c.2.2.2
                                                    linarith only [hlam, p44688_0]
                                              · linarith only [h44520, h44685, hlam]
                                          · linarith only [h44512, h44682, hlam]
                                        · linarith only [h41029, h44681, hlam]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h41029, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h44512, hlam, p44574_0]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        rcases p44574_3 (m.d 0 2) (by simp) with h44768 | h44768
                                        · rcases p44574_3 (m.d 1 2) (by simp) with h44769 | h44769
                                          · rcases p44574_3 (m.d 2 3) (by simp) with h44770 | h44770
                                            · linarith only [h44518, h44770, hlam]
                                            · rcases p44574_3 (m.d 2 4) (by simp) with h44772 | h44772
                                              · rcases p44574_3 (m.d 2 5) (by simp) with h44773 | h44773
                                                · rcases h4bigk with h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c | h44774c
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h36828, hlam, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h41030, h44510, h44513, h44520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h41030, hlam, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    rcases p44774_3 (m.d 0 4) (by simp) with h44779 | h44779
                                                    · rcases p44774_3 (m.d 1 4) (by simp) with h44780 | h44780
                                                      · rcases p44774_3 (m.d 2 4) (by simp) with h44781 | h44781
                                                        · linarith only [h41028, h44781, hlam]
                                                        · linarith only [h44520, h44781, hlam]
                                                      · linarith only [h44515, h44780, hlam]
                                                    · linarith only [h44779, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h41028, h44510, h44513, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44510, h44513, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h33187, h41030, h44510, h44513, hc01, hc12, hlam, hphi, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    rcases p44774_3 (m.d 0 4) (by simp) with h44790 | h44790
                                                    · linarith only [h36828, h44790, hlam]
                                                    · linarith only [h44509, h44790, hlam]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h41028, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44511, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44516, hlam, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    rcases p44774_3 (m.d 0 4) (by simp) with h44797 | h44797
                                                    · rcases p44774_3 (m.d 1 4) (by simp) with h44798 | h44798
                                                      · rcases p44774_3 (m.d 2 4) (by simp) with h44799 | h44799
                                                        · rcases p44774_3 (m.d 3 4) (by simp) with h44800 | h44800
                                                          · rcases p44774_3 (m.d 4 5) (by simp) with h44801 | h44801
                                                            · linarith only [h44801, hlam, p44774_0]
                                                            · rcases h5bigk with h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c | h44803c
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [hlam, p44803_0]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h39227, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p44574_1, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44266, hlam, p44803_0]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44266, h44510, h44513, h44521, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h39227, h44510, h44513, h44515, hc01, hc12, hlam, hphi, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [hlam, p44803_0]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44510, h44513, h44515, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h41029, h44266, h44510, h44513, h44515, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                rcases p44803_3 (m.d 0 5) (by simp) with h44813 | h44813
                                                                · linarith only [h39227, h44813, hlam]
                                                                · linarith only [h44509, h44813, hlam]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h41029, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44512, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [hlam, p44803_0]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44518, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h0, h41028, h44520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h39227, h44521, hc01, hc34, hlam, hphi, ht12, ht23, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44514, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44510, h44513, h44521, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [hlam, p44803_0]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44510, h44513, h44521, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44509, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44515, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44520, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [h44521, hlam, p44803_1]
                                                              · have p44803_0 := h44803c.1
                                                                have p44803_1 := h44803c.2.1
                                                                have p44803_2 := h44803c.2.2.1
                                                                have p44803_3 := h44803c.2.2.2
                                                                linarith only [hlam, p44803_0]
                                                          · linarith only [h44521, h44800, hlam]
                                                        · linarith only [h44799, hlam, p44774_0]
                                                      · linarith only [h44515, h44798, hlam]
                                                    · linarith only [h44509, h44797, hlam]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h41029, h44509, h44510, h44513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44513, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44510, h44513, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44574_1, p44774_1]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    rcases p44774_3 (m.d 0 4) (by simp) with h44839 | h44839
                                                    · linarith only [h41030, h44839, hlam]
                                                    · linarith only [h44509, h44839, hlam]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44509, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44515, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44520, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [h44521, hlam, p44774_0]
                                                  · have p44774_0 := h44774c.1
                                                    have p44774_1 := h44774c.2.1
                                                    have p44774_2 := h44774c.2.2.1
                                                    have p44774_3 := h44774c.2.2.2
                                                    linarith only [hlam, p44774_0]
                                                · linarith only [h44518, h44773, hlam]
                                              · linarith only [h44516, h44772, hlam]
                                          · linarith only [h44510, h44769, hlam]
                                        · linarith only [h41027, h44768, hlam]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [h44520, hlam, p44574_1]
                                      · have p44574_0 := h44574c.1
                                        have p44574_1 := h44574c.2.1
                                        have p44574_2 := h44574c.2.2.1
                                        have p44574_3 := h44574c.2.2.2
                                        linarith only [hlam, p44574_0]
                                    · linarith only [h0, h44573, hc01, hlam]
                                    · linarith only [h44513, h44515, h44573, hc01, hlam, p44522_1]
                                    · linarith only [h44515, h44573, hc01, hlam, p44522_1]
                                    · linarith only [h44573, hc01, hlam, p44522_1]
                                  · linarith only [h44572, hlam, p44522_0]
                                · linarith only [h36828, h44571, hlam]
                              · linarith only [h33187, h44570, hlam]
                            · linarith only [h0, h44569, hlam]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h44512, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h44514, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [h44515, hlam, p44522_0]
                        · have p44522_0 := h44522c.1
                          have p44522_1 := h44522c.2.1
                          have p44522_2 := h44522c.2.2.1
                          have p44522_3 := h44522c.2.2.2
                          linarith only [hlam, p44522_0]
                      · linarith only [h41030, h44509, h44521, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h44866 | h44866
                      · rcases h1bigk with h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c | h44867c
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h0, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h33187, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h36828, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h39227, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          rcases p44867_3 (m.d 0 1) (by simp) with h44873 | h44873
                          · linarith only [h44873, hlam, p44867_0]
                          · rcases p44867_3 (m.d 1 2) (by simp) with h44875 | h44875
                            · rcases p44867_3 (m.d 1 3) (by simp) with h44876 | h44876
                              · linarith only [h44510, h44876, hlam]
                              · linarith only [h33187, h44876, hlam]
                            · linarith only [h44875, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h41030, h44509, h44513, h44516, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h36828, hc01, hc12, hlam, hphi, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          rcases p44867_3 (m.d 0 1) (by simp) with h44884 | h44884
                          · linarith only [h44884, hlam, p44867_0]
                          · rcases p44867_3 (m.d 1 2) (by simp) with h44886 | h44886
                            · rcases p44867_3 (m.d 1 3) (by simp) with h44887 | h44887
                              · rcases p44867_3 (m.d 1 4) (by simp) with h44888 | h44888
                                · linarith only [h44513, h44888, hlam]
                                · linarith only [h36828, h44888, hlam]
                              · linarith only [h44887, hlam, p44867_0]
                            · linarith only [h0, h44886, hlam]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h44510, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h41030, h44509, h44513, h44516, h44520, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h33187, h44266, h44510, h44514, hc01, hc12, hlam, hphi, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          rcases p44867_3 (m.d 0 1) (by simp) with h44897 | h44897
                          · linarith only [h44897, hlam, p44867_0]
                          · rcases p44867_3 (m.d 1 2) (by simp) with h44899 | h44899
                            · rcases p44867_3 (m.d 1 3) (by simp) with h44900 | h44900
                              · rcases p44867_3 (m.d 1 4) (by simp) with h44901 | h44901
                                · rcases p44867_3 (m.d 1 5) (by simp) with h44902 | h44902
                                  · linarith only [h44515, h44902, hlam]
                                  · linarith only [h39227, h44902, hlam]
                                · linarith only [h44901, hlam, p44867_0]
                              · linarith only [h33187, h44900, hlam]
                            · linarith only [h0, h44899, hlam]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h44511, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h44513, hlam, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h33187, h44266, h44514, hc01, hc14, hlam, hphi, p44867_1]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          rcases p44867_3 (m.d 0 1) (by simp) with h44912 | h44912
                          · linarith only [h44912, hlam, p44867_0]
                          · rcases p44867_3 (m.d 1 2) (by simp) with h44914 | h44914
                            · rcases p44867_3 (m.d 1 3) (by simp) with h44915 | h44915
                              · rcases p44867_3 (m.d 1 4) (by simp) with h44916 | h44916
                                · rcases p44867_3 (m.d 1 5) (by simp) with h44917 | h44917
                                  · rcases h1emax with h44918 | h44918 | h44918 | h44918 | h44918
                                    · rcases h2bigk with h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c | h44919c
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h0, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        rcases p44919_3 (m.d 0 2) (by simp) with h44922 | h44922
                                        · rcases p44919_3 (m.d 1 2) (by simp) with h44923 | h44923
                                          · rcases p44919_3 (m.d 2 3) (by simp) with h44924 | h44924
                                            · linarith only [h44924, hlam, p44919_0]
                                            · rcases p44919_3 (m.d 2 4) (by simp) with h44926 | h44926
                                              · linarith only [h41028, h44926, hlam]
                                              · linarith only [h44516, h44926, hlam]
                                          · linarith only [h44510, h44923, hlam]
                                        · linarith only [h44922, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        rcases p44919_3 (m.d 0 2) (by simp) with h44931 | h44931
                                        · rcases p44919_3 (m.d 1 2) (by simp) with h44932 | h44932
                                          · rcases p44919_3 (m.d 2 3) (by simp) with h44933 | h44933
                                            · linarith only [h41027, h44933, hlam]
                                            · rcases p44919_3 (m.d 2 4) (by simp) with h44935 | h44935
                                              · linarith only [h44935, hlam, p44919_0]
                                              · rcases p44919_3 (m.d 2 5) (by simp) with h44937 | h44937
                                                · linarith only [h41029, h44937, hlam]
                                                · linarith only [h44520, h44937, hlam]
                                          · linarith only [h44511, h44932, hlam]
                                        · linarith only [h44931, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        rcases p44919_3 (m.d 0 2) (by simp) with h44942 | h44942
                                        · rcases p44919_3 (m.d 1 2) (by simp) with h44943 | h44943
                                          · rcases p44919_3 (m.d 2 3) (by simp) with h44944 | h44944
                                            · linarith only [h41027, h44944, hlam]
                                            · rcases p44919_3 (m.d 2 4) (by simp) with h44946 | h44946
                                              · linarith only [h41028, h44946, hlam]
                                              · rcases p44919_3 (m.d 2 5) (by simp) with h44948 | h44948
                                                · linarith only [h44948, hlam, p44919_0]
                                                · rcases h4bigk with h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c | h44950c
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h36828, hlam, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    rcases p44950_3 (m.d 0 4) (by simp) with h44953 | h44953
                                                    · rcases p44950_3 (m.d 1 4) (by simp) with h44954 | h44954
                                                      · rcases p44950_3 (m.d 2 4) (by simp) with h44955 | h44955
                                                        · linarith only [h41028, h44955, hlam]
                                                        · rcases p44950_3 (m.d 3 4) (by simp) with h44957 | h44957
                                                          · rcases p44950_3 (m.d 4 5) (by simp) with h44958 | h44958
                                                            · linarith only [h44509, h44958, hlam]
                                                            · linarith only [h44520, h44958, hlam]
                                                          · linarith only [h44516, h44957, hlam]
                                                      · linarith only [h44511, h44954, hlam]
                                                    · linarith only [h41028, h44953, hlam]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h41030, hlam, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h41030, h44516, h44520, hc23, hc34, hlam, hphi, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44509, h44510, h44513, h44516, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    rcases p44950_3 (m.d 0 4) (by simp) with h44968 | h44968
                                                    · linarith only [h36828, h44968, hlam]
                                                    · linarith only [h41028, h44968, hlam]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h33187, h41030, hc01, hc14, hlam, hphi, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    rcases p44950_3 (m.d 0 4) (by simp) with h44972 | h44972
                                                    · linarith only [h36828, h44972, hlam]
                                                    · linarith only [h44509, h44972, hlam]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h41028, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44511, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44516, hlam, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44520, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44509, h44516, h44520, hc23, hc34, hlam, hphi, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44513, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    rcases p44950_3 (m.d 0 4) (by simp) with h44982 | h44982
                                                    · linarith only [h41030, h44982, hlam]
                                                    · linarith only [h41028, h44982, hlam]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44510, h44513, h44516, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44509, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44515, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h41030, h44509, h44510, h44513, h44516, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44950_1]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [h44866, hlam, p44950_0]
                                                  · have p44950_0 := h44950c.1
                                                    have p44950_1 := h44950c.2.1
                                                    have p44950_2 := h44950c.2.2.1
                                                    have p44950_3 := h44950c.2.2.2
                                                    linarith only [hlam, p44950_0]
                                          · linarith only [h44512, h44943, hlam]
                                        · linarith only [h44942, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41028, h44509, h44516, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44919_1]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41030, h44509, h44510, h44513, h44516, h44520, hlam, p44919_2]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41030, h44509, h44510, h44513, h44520, hlam, p44919_2]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        rcases p44919_3 (m.d 0 2) (by simp) with h44998 | h44998
                                        · linarith only [h0, h44998, hlam]
                                        · linarith only [h41029, h44998, hlam]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41027, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h44510, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h44516, hlam, p44919_1]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h44518, hlam, p44919_1]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41028, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h44511, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41030, h44509, h44510, h44513, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44919_1]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h44520, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41029, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h44512, hlam, p44919_0]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41030, h44509, h44510, h44513, h44520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p44919_1]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [h41030, h44509, h44510, h44513, h44520, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p44919_1]
                                      · have p44919_0 := h44919c.1
                                        have p44919_1 := h44919c.2.1
                                        have p44919_2 := h44919c.2.2.1
                                        have p44919_3 := h44919c.2.2.2
                                        linarith only [hlam, p44919_0]
                                    · linarith only [h41030, h44509, h44510, h44513, h44520, h44918, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h41030, h44509, h44513, h44516, h44520, h44918, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h44515, h44918, hc01, hlam, p44867_1]
                                    · linarith only [h44918, hc01, hlam, p44867_1]
                                  · linarith only [h44917, hlam, p44867_0]
                                · linarith only [h36828, h44916, hlam]
                              · linarith only [h33187, h44915, hlam]
                            · linarith only [h0, h44914, hlam]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h44512, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h44514, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [h44515, hlam, p44867_0]
                        · have p44867_0 := h44867c.1
                          have p44867_1 := h44867c.2.1
                          have p44867_2 := h44867c.2.2.1
                          have p44867_3 := h44867c.2.2.2
                          linarith only [hlam, p44867_0]
                      · linarith only [h41030, h44509, h44866, hlam]
              · linarith only [h36828, h41030, h44509, h44510, h44513, h44515, hc01, hc12, hlam, hphi]
            · linarith only [h33187, h41030, h44513, h44514, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h45031 | h45031
            · linarith only [h33187, h44266, h44513, h45031, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h45033 | h45033
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45034 | h45034
                · linarith only [h0, h33187, h41027, h44513, h45034, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h45036 | h45036
                  · linarith only [h33187, h45031, h45036, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h45038 | h45038
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45039 | h45039
                      · rcases h1bigk with h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c | h45040c
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h0, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h33187, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h36828, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h39227, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          rcases p45040_3 (m.d 0 1) (by simp) with h45046 | h45046
                          · linarith only [h45046, hlam, p45040_0]
                          · rcases p45040_3 (m.d 1 2) (by simp) with h45048 | h45048
                            · rcases p45040_3 (m.d 1 3) (by simp) with h45049 | h45049
                              · linarith only [h44510, h45049, hlam]
                              · linarith only [h33187, h45049, hlam]
                            · linarith only [h45048, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h33187, hc01, hc12, hlam, hphi, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h36828, hc01, hc12, hlam, hphi, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h45031, h45039, hc01, hc34, hlam, hphi, ht12, ht23, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h44510, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h44513, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h45031, hlam, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          rcases p45040_3 (m.d 0 1) (by simp) with h45062 | h45062
                          · linarith only [h45062, hlam, p45040_0]
                          · rcases p45040_3 (m.d 1 2) (by simp) with h45064 | h45064
                            · rcases p45040_3 (m.d 1 3) (by simp) with h45065 | h45065
                              · linarith only [h44513, h45065, hlam]
                              · linarith only [h33187, h45065, hlam]
                            · linarith only [h0, h45064, hlam]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h44511, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h33187, hc01, hc14, hlam, hphi, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h39227, h44513, hc01, hc34, hlam, hphi, ht12, ht23, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          rcases p45040_3 (m.d 0 1) (by simp) with h45073 | h45073
                          · linarith only [h45073, hlam, p45040_0]
                          · rcases p45040_3 (m.d 1 2) (by simp) with h45075 | h45075
                            · rcases p45040_3 (m.d 1 3) (by simp) with h45076 | h45076
                              · linarith only [h45031, h45076, hlam]
                              · linarith only [h33187, h45076, hlam]
                            · linarith only [h0, h45075, hlam]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h44512, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h33187, hc01, hc15, hlam, hphi, p45040_1]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [h45033, hlam, p45040_0]
                        · have p45040_0 := h45040c.1
                          have p45040_1 := h45040c.2.1
                          have p45040_2 := h45040c.2.2.1
                          have p45040_3 := h45040c.2.2.2
                          linarith only [hlam, p45040_0]
                      · linarith only [h36828, h44509, h44513, h45039, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45085 | h45085
                      · rcases h1bigk with h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c | h45086c
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h0, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h33187, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h36828, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h39227, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          rcases p45086_3 (m.d 0 1) (by simp) with h45092 | h45092
                          · linarith only [h45092, hlam, p45086_0]
                          · rcases p45086_3 (m.d 1 2) (by simp) with h45094 | h45094
                            · rcases p45086_3 (m.d 1 3) (by simp) with h45095 | h45095
                              · linarith only [h44510, h45095, hlam]
                              · linarith only [h33187, h45095, hlam]
                            · linarith only [h45094, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h33187, hc01, hc12, hlam, hphi, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h36828, h44509, h45034, h45038, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h45031, h45085, hc01, hc34, hlam, hphi, ht12, ht23, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h44510, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h44513, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h45031, hlam, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          rcases p45086_3 (m.d 0 1) (by simp) with h45108 | h45108
                          · linarith only [h45108, hlam, p45086_0]
                          · rcases p45086_3 (m.d 1 2) (by simp) with h45110 | h45110
                            · rcases p45086_3 (m.d 1 3) (by simp) with h45111 | h45111
                              · linarith only [h44513, h45111, hlam]
                              · linarith only [h33187, h45111, hlam]
                            · linarith only [h0, h45110, hlam]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h44511, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h33187, hc01, hc14, hlam, hphi, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h39227, h44509, h44513, h45034, h45038, hc23, hc34, hlam, hphi, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          rcases p45086_3 (m.d 0 1) (by simp) with h45119 | h45119
                          · linarith only [h45119, hlam, p45086_0]
                          · rcases p45086_3 (m.d 1 2) (by simp) with h45121 | h45121
                            · rcases p45086_3 (m.d 1 3) (by simp) with h45122 | h45122
                              · linarith only [h45031, h45122, hlam]
                              · linarith only [h33187, h45122, hlam]
                            · linarith only [h0, h45121, hlam]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h44512, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h33187, hc01, hc15, hlam, hphi, p45086_1]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [h45033, hlam, p45086_0]
                        · have p45086_0 := h45086c.1
                          have p45086_1 := h45086c.2.1
                          have p45086_2 := h45086c.2.2.1
                          have p45086_3 := h45086c.2.2.2
                          linarith only [hlam, p45086_0]
                      · linarith only [h36828, h44509, h44513, h45085, hlam]
              · linarith only [h36828, h44509, h45033, hlam]
        · linarith only [h0, h41029, h44512, hlam]
      · linarith only [h0, h41028, h44511, hlam]
    · linarith only [h0, h41027, h44510, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h45135 | h45135
    · rcases m.htr 1 2 4 (by decide) (by decide) with h45136 | h45136
      · rcases m.htr 1 2 5 (by decide) (by decide) with h45137 | h45137
        · rcases m.htr 1 3 4 (by decide) (by decide) with h45138 | h45138
          · rcases m.htr 1 3 5 (by decide) (by decide) with h45139 | h45139
            · rcases m.htr 1 4 5 (by decide) (by decide) with h45140 | h45140
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45141 | h45141
                · linarith only [h41027, h41030, h45141, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h45143 | h45143
                  · linarith only [h39227, h41027, h41030, h44266, h44509, h45140, h45143, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h45145 | h45145
                    · linarith only [h41028, h44509, h45145, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45147 | h45147
                      · linarith only [h33187, h41030, h44509, h45135, h45138, h45147, hc01, hc12, hlam, hphi]
                      · linarith only [h33187, h41030, h45135, h45138, h45140, h45147, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45150 | h45150
                · linarith only [h41027, h41030, h45150, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h45152 | h45152
                  · linarith only [h41027, h44266, h45152, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h45154 | h45154
                    · linarith only [h36828, h45140, h45154, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45156 | h45156
                      · linarith only [h45138, h45140, h45156, hlam]
                      · rcases h1bigk with h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c | h45158c
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h0, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h33187, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h36828, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h39227, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          rcases p45158_3 (m.d 0 1) (by simp) with h45164 | h45164
                          · linarith only [h45164, hlam, p45158_0]
                          · rcases p45158_3 (m.d 1 2) (by simp) with h45166 | h45166
                            · rcases p45158_3 (m.d 1 3) (by simp) with h45167 | h45167
                              · linarith only [h45135, h45167, hlam]
                              · linarith only [h33187, h45167, hlam]
                            · linarith only [h45166, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h33187, hc01, hc12, hlam, hphi, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h33187, h41030, h45138, hc01, hc12, hlam, hphi, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          rcases p45158_3 (m.d 0 1) (by simp) with h45175 | h45175
                          · linarith only [h45175, hlam, p45158_0]
                          · rcases p45158_3 (m.d 1 2) (by simp) with h45177 | h45177
                            · rcases p45158_3 (m.d 1 3) (by simp) with h45178 | h45178
                              · rcases p45158_3 (m.d 1 4) (by simp) with h45179 | h45179
                                · linarith only [h45138, h45179, hlam]
                                · linarith only [h36828, h45179, hlam]
                              · linarith only [h45178, hlam, p45158_0]
                            · linarith only [h0, h45177, hlam]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45135, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h33187, h41030, h45138, hc01, hc13, hlam, hphi, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h33187, h41030, h45135, h45138, h45140, hc01, hc12, hlam, hphi, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45140, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45136, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45138, hlam, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45140, hlam, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          rcases p45158_3 (m.d 0 1) (by simp) with h45193 | h45193
                          · linarith only [h45193, hlam, p45158_0]
                          · rcases p45158_3 (m.d 1 2) (by simp) with h45195 | h45195
                            · rcases p45158_3 (m.d 1 3) (by simp) with h45196 | h45196
                              · rcases p45158_3 (m.d 1 4) (by simp) with h45197 | h45197
                                · linarith only [h45140, h45197, hlam]
                                · linarith only [h36828, h45197, hlam]
                              · linarith only [h33187, h45196, hlam]
                            · linarith only [h0, h45195, hlam]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45137, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h45139, hlam, p45158_0]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [h33187, h41030, h45138, hc01, hc15, hlam, hphi, p45158_1]
                        · have p45158_0 := h45158c.1
                          have p45158_1 := h45158c.2.1
                          have p45158_2 := h45158c.2.2.1
                          have p45158_3 := h45158c.2.2.2
                          linarith only [hlam, p45158_0]
            · linarith only [h33187, h41030, h45138, h45139, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h45207 | h45207
            · linarith only [h33187, h44266, h45138, h45207, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h45209 | h45209
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45210 | h45210
                · linarith only [h41027, h41030, h44509, h45138, h45209, h45210, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h45212 | h45212
                  · linarith only [h41027, h44266, h45212, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h45214 | h45214
                    · linarith only [h41028, h44509, h45214, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45216 | h45216
                      · rcases h1bigk with h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c | h45217c
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h0, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h33187, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h36828, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h39227, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          rcases p45217_3 (m.d 0 1) (by simp) with h45223 | h45223
                          · linarith only [h45223, hlam, p45217_0]
                          · rcases p45217_3 (m.d 1 2) (by simp) with h45225 | h45225
                            · rcases p45217_3 (m.d 1 3) (by simp) with h45226 | h45226
                              · linarith only [h45135, h45226, hlam]
                              · linarith only [h33187, h45226, hlam]
                            · linarith only [h45225, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h33187, hc01, hc12, hlam, hphi, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h41030, h44509, h45209, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h39227, hc01, hc12, hlam, hphi, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45138, hc01, hc34, hlam, hphi, ht12, ht23, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45135, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45138, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45207, hlam, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          rcases p45217_3 (m.d 0 1) (by simp) with h45239 | h45239
                          · linarith only [h45239, hlam, p45217_0]
                          · rcases p45217_3 (m.d 1 2) (by simp) with h45241 | h45241
                            · rcases p45217_3 (m.d 1 3) (by simp) with h45242 | h45242
                              · linarith only [h45138, h45242, hlam]
                              · linarith only [h33187, h45242, hlam]
                            · linarith only [h0, h45241, hlam]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45136, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h33187, hc01, hc14, hlam, hphi, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h33187, h41030, h44509, h45138, h45209, hc01, hc34, hlam, hphi, ht12, ht23, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          rcases p45217_3 (m.d 0 1) (by simp) with h45250 | h45250
                          · linarith only [h45250, hlam, p45217_0]
                          · rcases p45217_3 (m.d 1 2) (by simp) with h45252 | h45252
                            · rcases p45217_3 (m.d 1 3) (by simp) with h45253 | h45253
                              · linarith only [h45207, h45253, hlam]
                              · linarith only [h33187, h45253, hlam]
                            · linarith only [h0, h45252, hlam]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45137, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h33187, hc01, hc15, hlam, hphi, p45217_1]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [h45209, hlam, p45217_0]
                        · have p45217_0 := h45217c.1
                          have p45217_1 := h45217c.2.1
                          have p45217_2 := h45217c.2.2.1
                          have p45217_3 := h45217c.2.2.2
                          linarith only [hlam, p45217_0]
                      · linarith only [h33187, h45138, h45216, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45262 | h45262
                · linarith only [h33187, h45138, h45262, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h45264 | h45264
                  · linarith only [h41027, h44266, h45264, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h45266 | h45266
                    · linarith only [h36828, h41028, h45209, h45266, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45268 | h45268
                      · linarith only [h33187, h45138, h45209, h45268, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h33187, h45138, h45268, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h41029, h45137, hlam]
      · linarith only [h0, h41028, h45136, hlam]
    · linarith only [h0, h41027, h41028, h41030, h44509, h45135, hc24, hc45, hlam, hphi]

set_option maxHeartbeats 8488000 in
set_option maxHeartbeats 8488000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h41030 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  rcases m.htr 0 3 5 (by decide) (by decide) with h44266 | h44266
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 h41030 h44266
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 h41030 h44266

set_option maxHeartbeats 8488000 in
set_option maxHeartbeats 8488000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  rcases m.htr 0 3 4 (by decide) (by decide) with h41030 | h41030
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 h41030
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 h41030

end R2N4
