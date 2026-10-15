import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8273 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8274 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8275 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 3 5 (by decide) (by decide) with h8700 | h8700
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8701 | h8701
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8702 | h8702
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8703 | h8703
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8704 | h8704
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8705 | h8705
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8706 | h8706
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8707 | h8707
                · linarith only [h8272, h8275, h8707, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8709 | h8709
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8710 | h8710
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8711 | h8711
                      · rcases h0bigk with h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c | h8712c
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h0, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h5743, hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h6852, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h7594, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h0, h8272, h8709, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h5743, h8702, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8272, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8275, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h7594, h8275, h8702, h8705, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h6852, h8702, h8705, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8273, hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8275, h8702, h8705, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h7594, h8275, h8702, h8705, hc01, hc12, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8274, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8700, hlam, p8712_0]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [h8701, hlam, p8712_1]
                        · have p8712_0 := h8712c.1
                          have p8712_1 := h8712c.2.1
                          have p8712_2 := h8712c.2.2.1
                          have p8712_3 := h8712c.2.2.2
                          linarith only [hlam, p8712_0]
                      · linarith only [h8275, h8701, h8711, hlam]
                    · linarith only [h8275, h8700, h8701, h8702, h8705, h8707, h8709, h8710, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8275, h8700, h8702, h8705, h8709, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8275, h8700, h8705, h8706, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8742 | h8742
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8743 | h8743
                · linarith only [h7594, h8705, h8742, h8743, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8745 | h8745
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8746 | h8746
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8747 | h8747
                      · rcases h0bigk with h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c | h8748c
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h0, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h5743, hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h6852, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h7594, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8272, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8275, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h5743, h7594, h8705, hc01, hc34, hlam, hphi, ht12, ht23, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8275, hc01, hc34, hlam, hphi, ht12, ht23, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8273, hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8275, hc03, hc34, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h7594, h8275, hc01, hc34, hlam, hphi, ht12, ht23, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8274, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8700, hlam, p8748_0]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [h8701, hlam, p8748_1]
                        · have p8748_0 := h8748c.1
                          have p8748_1 := h8748c.2.1
                          have p8748_2 := h8748c.2.2.1
                          have p8748_3 := h8748c.2.2.2
                          linarith only [hlam, p8748_0]
                      · linarith only [h5743, h8705, h8747, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h8743, h8745, h8746, hlam]
                  · linarith only [h5743, h8700, h8705, h8745, hc23, hc34, hlam, hphi]
              · linarith only [h5743, h8700, h8742, hlam]
          · linarith only [h0, h8274, h8704, hlam]
        · linarith only [h0, h8273, h8703, hlam]
      · linarith only [h0, h8272, h8702, hlam]
    · linarith only [h8275, h8700, h8701, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8782 | h8782
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8783 | h8783
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8784 | h8784
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8785 | h8785
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8786 | h8786
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8787 | h8787
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8788 | h8788
                · linarith only [h8272, h8275, h8788, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8790 | h8790
                  · linarith only [h8272, h8700, h8790, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8792 | h8792
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8793 | h8793
                      · rcases h0bigk with h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c | h8794c
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [hlam, p8794_0]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h0, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h5743, hlam, p8794_0]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h6852, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h7594, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [hlam, p8794_0]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h0, h5743, h8700, h8782, hc01, hc12, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h0, h5743, h8700, hc01, hc12, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8700, h8786, h8793, hc01, hc13, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8272, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [hlam, p8794_0]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8275, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8700, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h6852, hc01, hc14, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8273, hlam, p8794_0]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8275, h8786, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [hlam, p8794_0]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h5743, h8275, h8700, h8786, hc01, hc13, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8274, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h5743, h8700, h8786, h8793, hc01, hc13, hlam, hphi, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [h8782, hlam, p8794_1]
                        · have p8794_0 := h8794c.1
                          have p8794_1 := h8794c.2.1
                          have p8794_2 := h8794c.2.2.1
                          have p8794_3 := h8794c.2.2.2
                          linarith only [hlam, p8794_0]
                      · linarith only [h0, h6852, h8273, h8275, h8792, h8793, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8821 | h8821
                      · rcases h0bigk with h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [hlam, p8822_0]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h0, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h5743, hlam, p8822_0]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h6852, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h7594, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [hlam, p8822_0]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h0, h8782, h8788, h8792, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h0, h8782, h8788, h8792, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8700, hc01, hc35, hlam, hphi, ht12, ht23, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8272, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [hlam, p8822_0]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8275, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8700, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8275, hc01, hc34, hlam, hphi, ht12, ht23, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8273, hlam, p8822_0]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8275, hc03, hc34, hlam, hphi, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [hlam, p8822_0]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8275, h8782, h8788, h8792, hc23, hc34, hlam, hphi, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h7594, h8783, h8787, hc01, hc12, hlam, hphi, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8274, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h5743, h7594, h8783, h8787, hc01, hc12, hlam, hphi, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [h8782, hlam, p8822_1]
                        · have p8822_0 := h8822c.1
                          have p8822_1 := h8822c.2.1
                          have p8822_2 := h8822c.2.2.1
                          have p8822_3 := h8822c.2.2.2
                          linarith only [hlam, p8822_0]
                      · linarith only [h8275, h8782, h8821, hlam]
              · linarith only [h5743, h8275, h8786, h8787, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8850 | h8850
              · linarith only [h5743, h8700, h8786, h8850, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8852 | h8852
                · linarith only [h5743, h8786, h8852, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8854 | h8854
                  · linarith only [h0, h7594, h8272, h8850, h8854, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8856 | h8856
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8857 | h8857
                      · rcases h0bigk with h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [hlam, p8858_0]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h0, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h5743, hlam, p8858_0]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h6852, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h7594, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [hlam, p8858_0]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h8272, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [hlam, p8858_0]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h8275, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h8700, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h6852, h8786, hc01, hc34, hlam, hphi, ht12, ht23, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h8273, hlam, p8858_0]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h6852, h8786, hc03, hc34, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [hlam, p8858_0]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h6852, h7594, h8786, hc01, hc34, hlam, hphi, ht12, ht23, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h8274, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h5743, h8700, hc01, hc35, hlam, hphi, ht12, ht23, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [h8782, hlam, p8858_1]
                        · have p8858_0 := h8858c.1
                          have p8858_1 := h8858c.2.1
                          have p8858_2 := h8858c.2.2.1
                          have p8858_3 := h8858c.2.2.2
                          linarith only [hlam, p8858_0]
                      · linarith only [h0, h6852, h8273, h8786, h8856, h8857, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8885 | h8885
                      · rcases h0bigk with h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c | h8886c
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [hlam, p8886_0]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h0, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h5743, hlam, p8886_0]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h6852, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h7594, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [hlam, p8886_0]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h0, h8782, h8852, h8856, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8272, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [hlam, p8886_0]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8275, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8700, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h6852, hc01, hc14, hlam, hphi, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8273, hlam, p8886_0]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8275, hc03, hc34, hlam, hphi, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [hlam, p8886_0]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h5743, h8275, h8700, hc01, hc34, hlam, hphi, ht12, ht23, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h7594, h8850, h8885, hc01, hc34, hlam, hphi, ht12, ht23, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8274, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h5743, h7594, h8850, h8885, hc01, hc34, hlam, hphi, ht12, ht23, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [h8782, hlam, p8886_1]
                        · have p8886_0 := h8886c.1
                          have p8886_1 := h8886c.2.1
                          have p8886_2 := h8886c.2.2.1
                          have p8886_3 := h8886c.2.2.2
                          linarith only [hlam, p8886_0]
                      · linarith only [h6852, h8782, h8786, h8885, hlam]
          · linarith only [h0, h8274, h8785, hlam]
        · linarith only [h0, h8273, h8784, hlam]
      · linarith only [h0, h8272, h8783, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8916 | h8916
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8917 | h8917
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8918 | h8918
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8919 | h8919
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8920 | h8920
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8921 | h8921
                · linarith only [h8272, h8275, h8921, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8923 | h8923
                  · linarith only [h8272, h8700, h8923, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8925 | h8925
                    · linarith only [h8273, h8782, h8925, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8927 | h8927
                      · linarith only [h5743, h8275, h8782, h8916, h8919, h8927, hc01, hc12, hlam, hphi]
                      · rcases h0bigk with h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c | h8929c
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h0, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h5743, hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h6852, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h7594, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h0, h5743, h8275, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h0, h5743, h8275, h8782, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8275, hc01, hc34, hlam, hphi, ht12, ht23, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8272, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8275, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8700, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h6852, h8916, h8919, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8273, hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h5743, h7594, h8782, h8916, h8920, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8782, hlam, p8929_0]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h7594, h8916, h8920, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h8274, hlam, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h5743, h7594, h8916, h8920, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [h6852, h7594, h8916, h8920, hc01, hc12, hlam, hphi, p8929_1]
                        · have p8929_0 := h8929c.1
                          have p8929_1 := h8929c.2.1
                          have p8929_2 := h8929c.2.2.1
                          have p8929_3 := h8929c.2.2.2
                          linarith only [hlam, p8929_0]
              · linarith only [h5743, h8275, h8919, h8920, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8956 | h8956
              · linarith only [h5743, h8700, h8919, h8956, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8958 | h8958
                · linarith only [h5743, h8919, h8958, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8960 | h8960
                  · linarith only [h0, h7594, h8272, h8956, h8960, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8962 | h8962
                    · linarith only [h8273, h8782, h8962, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8964 | h8964
                      · rcases h0bigk with h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c | h8965c
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h0, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h5743, hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h6852, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h7594, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h0, h5743, hc01, hc12, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h0, h6852, hc01, hc12, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h0, h7594, hc01, hc12, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h5743, hc01, hc13, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8272, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8275, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8700, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8782, h8964, hc01, hc34, hlam, hphi, ht12, ht23, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8273, hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8782, h8964, hc03, hc34, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8782, hlam, p8965_0]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h7594, hc01, hc15, hlam, hphi, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8274, hlam, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h5743, h8700, hc01, hc35, hlam, hphi, ht12, ht23, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [h8782, h8964, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p8965_1]
                        · have p8965_0 := h8965c.1
                          have p8965_1 := h8965c.2.1
                          have p8965_2 := h8965c.2.2.1
                          have p8965_3 := h8965c.2.2.2
                          linarith only [hlam, p8965_0]
                      · linarith only [h5743, h8919, h8964, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8274, h8918, hlam]
        · linarith only [h0, h8273, h8917, hlam]
      · linarith only [h0, h8272, h8916, hlam]

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8273 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8274 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 3 4 (by decide) (by decide) with h8275 | h8275
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h8273 h8274 h8275
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h8273 h8274 h8275

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8273 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8274 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 3 4 (by decide) (by decide) with h8995 | h8995
  · rcases m.htr 0 3 5 (by decide) (by decide) with h8996 | h8996
    · linarith only [h8272, h8274, h8996, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h8998 | h8998
      · linarith only [h8273, h8274, h8998, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9000 | h9000
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9001 | h9001
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9002 | h9002
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9003 | h9003
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9004 | h9004
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9005 | h9005
                  · linarith only [h8272, h8274, h9002, h9005, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h8272, h8274, h8995, h9002, h9005, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9008 | h9008
                  · linarith only [h8272, h8274, h9002, h9008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h8272, h8274, h8995, h9002, h9008, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h5743, h8272, h8274, h8995, h9002, h9003, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9012 | h9012
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9013 | h9013
                · linarith only [h8995, h8996, h9000, h9002, h9013, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9015 | h9015
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9016 | h9016
                    · linarith only [h8272, h8274, h8998, h9013, h9016, hc13, hc45, hlam, hphi, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9018 | h9018
                      · linarith only [h0, h7594, h8273, h8998, h9002, h9016, h9018, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h8272, h9002, h9015, h9018, hc34, hc45, hlam, hphi]
                  · linarith only [h8995, h8996, h9015, hc23, hc35, hlam, hphi]
              · linarith only [h5743, h8995, h9012, hlam]
          · linarith only [h0, h8273, h9001, hlam]
        · linarith only [h0, h8272, h9000, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9025 | h9025
    · linarith only [h8273, h8274, h8995, h9025, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9027 | h9027
      · linarith only [h8273, h8274, h9027, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9029 | h9029
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9030 | h9030
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9031 | h9031
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9032 | h9032
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9033 | h9033
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9034 | h9034
                  · linarith only [h0, h5743, h8272, h8995, h9034, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9036 | h9036
                    · linarith only [h5743, h8273, h8274, h9025, h9031, h9034, h9036, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9038 | h9038
                      · linarith only [h8273, h8274, h9029, h9033, h9036, h9038, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9040 | h9040
                        · linarith only [h8273, h8274, h9034, h9038, h9040, hc23, hc34, hlam, hphi]
                        · rcases h0bigk with h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c | h9042c
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h0, hlam, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h5743, hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h6852, hlam, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h7594, hlam, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8274, h9029, h9033, h9036, hc01, hc12, hlam, hphi, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h5743, h8274, h9029, h9033, h9036, hc01, hc12, hlam, hphi, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8274, h9029, h9033, h9036, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8274, hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h5743, h9029, hc01, hc12, hlam, hphi, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8272, hlam, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8995, hlam, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h9025, hlam, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h6852, hc01, hc14, hlam, hphi, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8273, hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8273, h8274, h9029, h9033, h9036, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h9027, hlam, p9042_0]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h7594, hc01, hc15, hlam, hphi, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8274, h9029, h9033, h9036, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h5743, h8274, h9029, h9033, h9036, hc01, hc12, hlam, hphi, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [h8274, h9029, h9033, h9036, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9042_1]
                          · have p9042_0 := h9042c.1
                            have p9042_1 := h9042c.2.1
                            have p9042_2 := h9042c.2.2.1
                            have p9042_3 := h9042c.2.2.2
                            linarith only [hlam, p9042_0]
                · linarith only [h5743, h8995, h9032, h9033, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9069 | h9069
                · linarith only [h5743, h9025, h9032, h9069, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9071 | h9071
                  · linarith only [h5743, h9032, h9071, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9073 | h9073
                    · linarith only [h8273, h8274, h9031, h9069, h9071, h9073, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9075 | h9075
                      · linarith only [h8273, h8274, h9031, h9075, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9077 | h9077
                        · linarith only [h8273, h8274, h9071, h9075, h9077, hc23, hc34, hlam, hphi]
                        · linarith only [h5743, h9032, h9077, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9080 | h9080
              · linarith only [h5743, h8995, h9029, h9031, h9080, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9082 | h9082
                · linarith only [h5743, h9025, h9030, h9031, h9080, h9082, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9084 | h9084
                  · linarith only [h5743, h9080, h9084, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9086 | h9086
                    · linarith only [h0, h7594, h8273, h9031, h9082, h9084, h9086, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9088 | h9088
                      · linarith only [h0, h8273, h8995, h9027, h9031, h9086, h9088, hc03, hc35, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9090 | h9090
                        · linarith only [h0, h9031, h9088, h9090, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h5743, h9080, h9090, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h7594, h8273, h8274, h9030, hc01, hc15, hlam, hphi]
        · linarith only [h0, h8272, h9029, hlam]

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8273 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 5 (by decide) (by decide) with h8274 | h8274
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h8273 h8274
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h8273 h8274

end R2N4
