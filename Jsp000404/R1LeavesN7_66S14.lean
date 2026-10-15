import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S13

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_H_I_L_R_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h649 | h649
  · rcases m.htr 0 2 4 (by decide) (by decide) with h650 | h650
    · rcases m.htr 0 2 5 (by decide) (by decide) with h651 | h651
      · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
        · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
          · rcases m.htr 1 2 5 (by decide) (by decide) with h654 | h654
            · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
              · rcases m.htr 1 3 5 (by decide) (by decide) with h656 | h656
                · rcases m.htr 1 4 5 (by decide) (by decide) with h657 | h657
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h660 | h660
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h661 | h661
                          · rcases h2bigk with h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c | h662c
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h0, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h0, h658, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h0, h658, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h0, h659, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p662_1]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h658, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h658, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h659, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h649, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h652, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h649, h658, h661, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h0, h649, h659, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h650, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h653, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h658, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h650, h659, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p662_1, u3ehi4]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h651, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h654, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h659, hlam, p662_0]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [h660, hlam, p662_1]
                            · have p662_0 := h662c.1
                              have p662_1 := h662c.2.1
                              have p662_2 := h662c.2.2.1
                              have p662_3 := h662c.2.2.2
                              linarith only [hlam, p662_0]
                          · linarith only [h0, h649, h658, h660, h661, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h689 | h689
                          · linarith only [h658, h660, h689, hlam]
                          · rcases h2bigk with h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h0, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi2]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h0, h658, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h0, h658, h660, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p691_1]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi2]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h658, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h658, h660, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h649, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h652, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h649, h658, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h0, h649, h658, h660, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h650, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h653, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h658, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h660, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h651, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h654, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h659, hlam, p691_0]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [h651, h658, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u3ehi3]
                            · have p691_0 := h691c.1
                              have p691_1 := h691c.2.1
                              have p691_2 := h691c.2.2.1
                              have p691_3 := h691c.2.2.2
                              linarith only [hlam, p691_0]
                      · linarith only [h652, h656, h658, h659, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h718 | h718
                      · linarith only [h658, h718, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h720 | h720
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h721 | h721
                          · rcases h2bigk with h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h0, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h0, h718, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h0, h718, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p722_1]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h718, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h718, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h649, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h652, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h658, hlam, p722_1]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h718, hlam, p722_1]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h650, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h653, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h650, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h652, h655, h658, h718, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h651, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h654, hlam, p722_0]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p722_1, u3ehi2]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [h720, hlam, p722_1]
                            · have p722_0 := h722c.1
                              have p722_1 := h722c.2.1
                              have p722_2 := h722c.2.2.1
                              have p722_3 := h722c.2.2.2
                              linarith only [hlam, p722_0]
                          · linarith only [h658, h720, h721, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h749 | h749
                          · linarith only [h652, h655, h658, h720, h749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h652, h655, h657, h658, h749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h754 | h754
                        · linarith only [h653, h657, h754, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h756 | h756
                          · linarith only [h653, h657, h752, h756, hlam]
                          · rcases h2bigk with h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi2]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, h752, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi3]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, h753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi4]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p758_1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi4]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h752, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi3]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi4]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h649, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h652, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h649, h752, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p758_1, u3ehi3]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, h649, h753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p758_1, u3ehi4]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h650, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h653, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h752, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h754, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h651, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h654, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h753, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h752, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p758_1, u3ehi3]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                      · linarith only [h652, h656, h752, h753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h655, h657, h752, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h655, h656, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                · linarith only [h655, h787, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h789 | h789
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h790 | h790
                    · linarith only [h0, h649, h655, h790, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h792 | h792
                      · linarith only [h652, h655, h792, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h794 | h794
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h795 | h795
                          · rcases h2bigk with h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h0, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h0, h792, h794, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h0, h792, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h649, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h792, h794, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h792, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h649, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h652, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h790, hlam, p796_1]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h792, hlam, p796_1]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h650, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h653, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h650, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h0, h650, h792, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h651, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h654, hlam, p796_0]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p796_1, u3ehi2]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [h794, hlam, p796_1]
                            · have p796_0 := h796c.1
                              have p796_1 := h796c.2.1
                              have p796_2 := h796c.2.2.1
                              have p796_3 := h796c.2.2.2
                              linarith only [hlam, p796_0]
                          · linarith only [h0, h650, h794, h795, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h655, h789, h790, h794, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h824 | h824
                    · linarith only [h652, h655, h824, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h826 | h826
                      · linarith only [h652, h655, h789, h826, hc45, hlam, hphi, ht34, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h828 | h828
                        · linarith only [h0, h650, h655, h789, h828, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                          · linarith only [h652, h655, h789, h830, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h652, h655, h830, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h0, h651, h654, hlam]
          · linarith only [h0, h650, h653, hlam]
        · linarith only [h0, h649, h652, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
        · rcases m.htr 1 2 4 (by decide) (by decide) with h837 | h837
          · rcases m.htr 1 2 5 (by decide) (by decide) with h838 | h838
            · linarith only [h649, h651, h838, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
              · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                · linarith only [h836, h838, h841, hlam]
                · linarith only [h840, h841, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h844 | h844
                · linarith only [h840, h844, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h846 | h846
                  · linarith only [h837, h838, h846, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h848 | h848
                    · linarith only [h649, h651, h848, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h850 | h850
                      · linarith only [h0, h650, h838, h844, h848, h850, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h649, h838, h850, hc35, hlam, hphi, u3ehi2]
          · linarith only [h0, h650, h837, hlam]
        · linarith only [h0, h649, h836, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h855 | h855
      · rcases m.htr 1 2 3 (by decide) (by decide) with h856 | h856
        · rcases m.htr 1 2 4 (by decide) (by decide) with h857 | h857
          · linarith only [h649, h650, h857, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h859 | h859
            · rcases m.htr 1 3 4 (by decide) (by decide) with h860 | h860
              · linarith only [h856, h857, h860, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h862 | h862
                · linarith only [h860, h862, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h864 | h864
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
                    · linarith only [h649, h860, h865, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h649, h857, h865, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h0, h649, h857, h864, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h0, h855, h859, hlam]
        · linarith only [h0, h649, h856, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
        · rcases m.htr 1 2 4 (by decide) (by decide) with h872 | h872
          · linarith only [h649, h650, h872, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
            · linarith only [h649, h855, h872, h874, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
              · linarith only [h871, h872, h876, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                · linarith only [h876, h878, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h880 | h880
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h881 | h881
                    · linarith only [h649, h876, h881, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h649, h872, h881, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h0, h649, h872, h880, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h0, h649, h871, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h886 | h886
    · rcases m.htr 0 2 5 (by decide) (by decide) with h887 | h887
      · rcases m.htr 1 2 3 (by decide) (by decide) with h888 | h888
        · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
          · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
            · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
              · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
                · rcases m.htr 1 4 5 (by decide) (by decide) with h893 | h893
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                    · linarith only [h649, h886, h888, h894, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h649, h886, h888, h891, h894, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h897 | h897
                    · linarith only [h649, h886, h888, h897, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h649, h886, h888, h891, h897, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h891, h892, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
                · linarith only [h891, h901, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h903 | h903
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h904 | h904
                    · linarith only [h888, h891, h904, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h649, h886, h904, hlam]
                  · linarith only [h649, h886, h888, h891, h903, hc24, hc45, hlam, hphi]
            · linarith only [h649, h887, h890, hc12, hc23, hlam, hphi]
          · linarith only [h649, h886, h888, h889, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h910 | h910
          · rcases m.htr 1 2 5 (by decide) (by decide) with h911 | h911
            · rcases m.htr 1 3 4 (by decide) (by decide) with h912 | h912
              · rcases m.htr 1 3 5 (by decide) (by decide) with h913 | h913
                · rcases m.htr 1 4 5 (by decide) (by decide) with h914 | h914
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h916 | h916
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
                          · rcases h2bigk with h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c | h919c
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h0, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h649, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h916, h917, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h0, h888, h916, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h888, hc02, hc23, hlam, hphi, p919_1]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h888, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h888, h916, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h888, h916, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h886, h916, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p919_1]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h916, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h916, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h886, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h910, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h915, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h886, h916, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p919_1, u3ehi4]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h887, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h911, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h916, hlam, p919_0]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [h917, hlam, p919_1]
                            · have p919_0 := h919c.1
                              have p919_1 := h919c.2.1
                              have p919_2 := h919c.2.2.1
                              have p919_3 := h919c.2.2.2
                              linarith only [hlam, p919_0]
                          · linarith only [h888, h910, h914, h918, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h888, h910, h914, h915, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h888, h916, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h888, h910, h913, h914, h915, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h951 | h951
                        · linarith only [h0, h886, h888, h914, h951, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h953 | h953
                          · linarith only [h910, h914, h949, h953, hlam]
                          · rcases h2bigk with h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h0, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h649, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h949, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p955_1, u3ehi3]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h0, h888, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h888, hc02, hc23, hlam, hphi, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h888, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h888, h949, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p955_1, u3ehi3]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h888, h950, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p955_1, u3ehi4]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h886, h949, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p955_1, u3ehi3]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h949, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p955_1, u3ehi3]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h950, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p955_1, u3ehi4]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h886, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h910, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h949, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h951, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h887, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h911, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h950, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h949, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p955_1, u3ehi3]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                      · linarith only [h649, h886, h949, h950, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h888, h949, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h912, h913, hc35, hlam, hphi, u3ehi3]
              · linarith only [h888, h910, h912, hlam]
            · linarith only [h0, h887, h911, hlam]
          · linarith only [h0, h886, h910, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
        · rcases m.htr 1 2 4 (by decide) (by decide) with h988 | h988
          · rcases m.htr 1 2 5 (by decide) (by decide) with h989 | h989
            · rcases m.htr 1 3 4 (by decide) (by decide) with h990 | h990
              · rcases m.htr 1 3 5 (by decide) (by decide) with h991 | h991
                · rcases m.htr 1 4 5 (by decide) (by decide) with h992 | h992
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                    · linarith only [h649, h886, h987, h993, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h649, h990, h993, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h996 | h996
                    · linarith only [h649, h886, h987, h996, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h649, h987, h990, h996, hc01, hc12, hlam, hphi]
                · linarith only [h990, h991, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1000 | h1000
                · linarith only [h1000, h990, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1002 | h1002
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1003 | h1003
                    · linarith only [h1003, h987, h990, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1003, h649, h886, hlam]
                  · linarith only [h1002, h649, h886, h987, h990, hc24, hc45, hlam, hphi]
            · linarith only [h649, h886, h987, h989, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h649, h886, h987, h988, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1009 | h1009
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1010 | h1010
            · linarith only [h1010, h886, h887, h987, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1012 | h1012
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1013 | h1013
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1014 | h1014
                  · linarith only [h1009, h1010, h1014, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1016 | h1016
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                        · linarith only [h0, h1010, h1014, h1017, h1018, h886, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1010, h1016, h1018, h886, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h1016, h1017, h649, h886, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h1016, h987, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1012, h1013, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1009, h1012, h987, hlam]
          · linarith only [h0, h1009, h886, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1026 | h1026
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1027 | h1027
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1028 | h1028
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1029 | h1029
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1030 | h1030
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1031 | h1031
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1032 | h1032
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1033 | h1033
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                      · linarith only [h1026, h1027, h1034, h649, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1033, h1034, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1026, h1030, h1033, h649, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1039 | h1039
                      · linarith only [h1026, h1028, h1032, h1039, h886, hc45, hlam, hphi, ht34, u3ehi4]
                      · linarith only [h1038, h1039, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1026, h1027, h1030, h1038, h649, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h1030, h1031, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1044 | h1044
                · linarith only [h1030, h1044, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1046 | h1046
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1047 | h1047
                    · linarith only [h1027, h1030, h1047, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1049 | h1049
                      · linarith only [h1027, h1044, h1049, hlam]
                      · linarith only [h1026, h1049, h649, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1052 | h1052
                    · linarith only [h1027, h1030, h1052, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1054 | h1054
                      · linarith only [h1027, h1044, h1054, hlam]
                      · linarith only [h1026, h1054, h649, hlam]
            · linarith only [h1026, h1029, h649, hc12, hc23, hlam, hphi]
          · linarith only [h1027, h1028, h649, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1059 | h1059
          · linarith only [h1026, h1027, h1059, h886, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1061 | h1061
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1062 | h1062
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1063 | h1063
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1064 | h1064
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1065 | h1065
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1066 | h1066
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1067 | h1067
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1068 | h1068
                          · rcases h2bigk with h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c | h1069c
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h0, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h649, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h886, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1066, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1059, h1065, hc02, hc23, hlam, hphi, p1069_1]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1027, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1059, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1059, h1065, h1066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1026, h1066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1069_1]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1026, h1066, h886, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1026, h1066, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h0, h1026, h1066, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1065, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1065, h1066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1069_1, u3ehi4]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1026, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1061, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1066, hlam, p1069_0]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [h1067, hlam, p1069_1]
                            · have p1069_0 := h1069c.1
                              have p1069_1 := h1069c.2.1
                              have p1069_2 := h1069c.2.2.1
                              have p1069_3 := h1069c.2.2.2
                              linarith only [hlam, p1069_0]
                          · linarith only [h0, h1026, h1059, h1065, h1067, h1068, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1059, h1067, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1059, h1065, h1066, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h1027, h1062, h1065, hc01, hc13, hlam, hphi]
                  · linarith only [h1059, h1061, h1064, hlam]
                · linarith only [h1062, h1063, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1101 | h1101
                · linarith only [h1062, h1101, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1027, h1061, h1101, hlam]
            · linarith only [h0, h1026, h1061, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1105 | h1105
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1106 | h1106
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1108 | h1108
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1109 | h1109
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1110 | h1110
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1111 | h1111
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1112 | h1112
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1113 | h1113
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1114 | h1114
                          · rcases h2bigk with h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h649, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h886, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1026, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1111, h1114, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi4]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h886, hc01, hc12, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h1026, hc01, hc12, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h1105, hc01, hc13, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1105, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h1105, h886, hc01, hc12, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h1026, h1105, hc01, hc12, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1106, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1111, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h1026, h1105, h1111, hc01, hc12, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h0, h1107, hc01, hc15, hlam, hphi, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1107, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1112, hlam, p1115_0]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [h1113, hlam, p1115_1]
                            · have p1115_0 := h1115c.1
                              have p1115_1 := h1115c.2.1
                              have p1115_2 := h1115c.2.2.1
                              have p1115_3 := h1115c.2.2.2
                              linarith only [hlam, p1115_0]
                          · linarith only [h1105, h1111, h1113, h1114, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1110, h1113, h886, hc01, hc14, hlam, hphi]
                      · linarith only [h0, h1105, h1109, h1112, h649, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h1105, h1108, h1111, h649, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1145 | h1145
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1146 | h1146
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1147 | h1147
                        · linarith only [h1106, h1110, h1147, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1149 | h1149
                          · linarith only [h0, h1106, h1110, h1145, h1149, h886, hc01, hc23, hlam, hphi, ht12]
                          · rcases h2bigk with h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h649, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h886, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1026, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1151_1, u3ehi2]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, h886, hc01, hc12, hlam, hphi, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, h1026, hc01, hc12, hlam, hphi, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1105, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, h1105, h886, hc01, hc12, hlam, hphi, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, h1026, h1105, hc01, hc12, hlam, hphi, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, h1106, hc01, hc14, hlam, hphi, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1106, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1145, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1147, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1107, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1146, hlam, p1151_0]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [h1105, h1146, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1151_1]
                            · have p1151_0 := h1151c.1
                              have p1151_1 := h1151c.2.1
                              have p1151_2 := h1151c.2.2.1
                              have p1151_3 := h1151c.2.2.2
                              linarith only [hlam, p1151_0]
                      · linarith only [h0, h1105, h1109, h1146, h649, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h1105, h1108, h1145, h649, hc01, hc12, hlam, hphi]
                · linarith only [h1108, h1109, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                · linarith only [h1108, h1180, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1182 | h1182
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1183 | h1183
                    · linarith only [h1105, h1108, h1183, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1185 | h1185
                      · linarith only [h1105, h1180, h1185, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1187 | h1187
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1188 | h1188
                          · rcases h2bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h649, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h886, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1026, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, h649, hc01, hc12, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, h1185, h1187, h649, hc01, hc12, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, h1185, h649, hc01, hc12, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, h1105, hc01, hc13, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1105, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1183, hlam, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1185, hlam, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1106, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1106, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1189_1, u3ehi2]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, h1106, h1185, h649, hc01, hc12, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1107, hlam, p1189_0]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h0, h1107, h649, hc01, hc12, hlam, hphi, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [h1187, hlam, p1189_1]
                            · have p1189_0 := h1189c.1
                              have p1189_1 := h1189c.2.1
                              have p1189_2 := h1189c.2.2.1
                              have p1189_3 := h1189c.2.2.2
                              linarith only [hlam, p1189_0]
                          · linarith only [h1106, h1187, h1188, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1182, h1187, h886, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1217 | h1217
                    · linarith only [h1105, h1108, h1182, h1217, hc45, hlam, hphi, ht34, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1219 | h1219
                      · linarith only [h1105, h1180, h1219, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1221 | h1221
                        · linarith only [h0, h1105, h1108, h1182, h1221, h649, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1223 | h1223
                          · linarith only [h0, h1105, h1108, h1182, h1223, h649, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h1105, h1108, h1223, h649, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h1105, h1107, h649, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h1105, h1106, h649, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
          · linarith only [h0, h1105, h1228, h886, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
            · linarith only [h0, h1026, h1105, h1230, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1234 | h1234
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1237 | h1237
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                          · rcases h2bigk with h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h649, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h886, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1026, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, h1230, h1235, h1237, hc01, hc23, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1105, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1228, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1230, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, h886, hc01, hc23, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, h1230, hc01, hc23, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1235, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, h1230, h1235, hc01, hc23, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1236, hlam, p1239_0]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [h1237, hlam, p1239_1]
                            · have p1239_0 := h1239c.1
                              have p1239_1 := h1239c.2.1
                              have p1239_2 := h1239c.2.2.1
                              have p1239_3 := h1239c.2.2.2
                              linarith only [hlam, p1239_0]
                          · rcases h2bigk with h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h649, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h886, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1026, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1105, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1228, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1230, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, h886, hc01, hc23, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, h1230, hc01, hc23, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1235, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, h1230, h1235, hc01, hc23, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1236, hlam, p1265_0]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [h1237, hlam, p1265_1]
                            · have p1265_0 := h1265c.1
                              have p1265_1 := h1265c.2.1
                              have p1265_2 := h1265c.2.2.1
                              have p1265_3 := h1265c.2.2.2
                              linarith only [hlam, p1265_0]
                        · linarith only [h0, h1232, h1234, h1237, h886, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h1105, h1236, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1105, h1233, h1235, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1295 | h1295
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1296 | h1296
                        · linarith only [h0, h1228, h1234, h1294, h1296, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h1228, h1296, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1233, h1295, h649, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h1105, h1232, h1294, hc01, hc14, hlam, hphi]
                · linarith only [h1232, h1233, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
                · linarith only [h1232, h1302, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1304 | h1304
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1305 | h1305
                    · linarith only [h0, h1105, h1232, h1305, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h1105, h1305, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1308 | h1308
                    · linarith only [h0, h1105, h1232, h1308, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h1105, h1308, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_22_13_H_I_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_H_I_L_R_x0 m hb2 hb3 h0
  · exact r1l7_22_13_H_I_L_R_x1 m hb2 hb3 h0

end R2N4
