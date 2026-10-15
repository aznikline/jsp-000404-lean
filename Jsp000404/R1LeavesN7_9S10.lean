import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4260 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4261 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4262 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h4709 | h4709
  · linarith only [h0, h4, h4709, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4711 | h4711
    · linarith only [h0, h3688, h4711, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h4713 | h4713
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4714 | h4714
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4715 | h4715
          · linarith only [h2, h4262, h4715, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4717 | h4717
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4718 | h4718
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4719 | h4719
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4720 | h4720
                  · linarith only [h2, h4262, h4713, h4720, hlam]
                  · rcases h3bigk with h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c | h4722c
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4724 | h4724
                      · rcases p4722_3 (m.d 1 3) (by simp) with h4725 | h4725
                        · linarith only [h1, h4725, hlam]
                        · rcases p4722_3 (m.d 2 3) (by simp) with h4727 | h4727
                          · rcases p4722_3 (m.d 3 4) (by simp) with h4728 | h4728
                            · linarith only [h4260, h4728, hlam]
                            · rcases p4722_3 (m.d 3 5) (by simp) with h4730 | h4730
                              · linarith only [h4261, h4730, hlam]
                              · rcases h4bigk with h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4262, h4717, h4719, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h3688, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4262, h4717, h4719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4262, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h2, hlam, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4711, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4715, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h3688, h4717, hc02, hc23, hlam, hphi, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4711, h4717, hc12, hc23, hlam, hphi, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  rcases p4732_3 (m.d 0 4) (by simp) with h4746 | h4746
                                  · linarith only [h3688, h4746, hlam]
                                  · linarith only [h4260, h4746, hlam]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h0, h3688, h4262, h4717, hc12, hc23, hlam, hphi, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4260, hlam, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4713, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4717, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4720, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h0, h3688, hc12, hc45, hlam, hphi, ht23, ht34, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4711, hc12, hc45, hlam, hphi, ht23, ht34, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4719, hlam, p4732_0]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [h4717, h4719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4732_1]
                                · have p4732_0 := h4732c.1
                                  have p4732_1 := h4732c.2.1
                                  have p4732_2 := h4732c.2.2.1
                                  have p4732_3 := h4732c.2.2.2
                                  linarith only [hlam, p4732_0]
                          · linarith only [h4709, h4727, hlam]
                      · linarith only [h1, h4724, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4, hlam, p4722_1]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4763 | h4763
                      · rcases p4722_3 (m.d 1 3) (by simp) with h4764 | h4764
                        · linarith only [h1, h4764, hlam]
                        · linarith only [h4713, h4764, hlam]
                      · linarith only [h4763, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4768 | h4768
                      · rcases p4722_3 (m.d 1 3) (by simp) with h4769 | h4769
                        · linarith only [h1, h4769, hlam]
                        · linarith only [h4714, h4769, hlam]
                      · linarith only [h4768, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h1, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4709, hlam, p4722_1]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4776 | h4776
                      · rcases p4722_3 (m.d 1 3) (by simp) with h4777 | h4777
                        · rcases p4722_3 (m.d 2 3) (by simp) with h4778 | h4778
                          · rcases p4722_3 (m.d 3 4) (by simp) with h4779 | h4779
                            · linarith only [h4779, hlam, p4722_0]
                            · rcases p4722_3 (m.d 3 5) (by simp) with h4781 | h4781
                              · linarith only [h4714, h4781, hlam]
                              · linarith only [h4720, h4781, hlam]
                          · linarith only [h4717, h4778, hlam]
                        · linarith only [h4777, hlam, p4722_0]
                      · linarith only [h4260, h4776, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4787 | h4787
                      · rcases p4722_3 (m.d 1 3) (by simp) with h4788 | h4788
                        · rcases p4722_3 (m.d 2 3) (by simp) with h4789 | h4789
                          · rcases p4722_3 (m.d 3 4) (by simp) with h4790 | h4790
                            · linarith only [h4713, h4790, hlam]
                            · rcases p4722_3 (m.d 3 5) (by simp) with h4792 | h4792
                              · linarith only [h4792, hlam, p4722_0]
                              · rcases h4bigk with h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h3688, h4711, h4717, hc12, hc23, hlam, hphi, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h3688, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4262, h4717, h4719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4262, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h2, hlam, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4711, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4715, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h0, h3688, h4717, hc12, hc23, hlam, hphi, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4711, h4717, hc12, hc23, hlam, hphi, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  rcases p4794_3 (m.d 0 4) (by simp) with h4808 | h4808
                                  · linarith only [h3688, h4808, hlam]
                                  · linarith only [h4260, h4808, hlam]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h0, h3688, h4262, h4717, hc12, hc23, hlam, hphi, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4260, hlam, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4713, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4717, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4720, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h0, h3688, hc12, hc45, hlam, hphi, ht23, ht34, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4711, hc12, hc45, hlam, hphi, ht23, ht34, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4719, hlam, p4794_0]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [h4717, h4719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4794_1]
                                · have p4794_0 := h4794c.1
                                  have p4794_1 := h4794c.2.1
                                  have p4794_2 := h4794c.2.2.1
                                  have p4794_3 := h4794c.2.2.2
                                  linarith only [hlam, p4794_0]
                          · linarith only [h4718, h4789, hlam]
                        · linarith only [h4788, hlam, p4722_0]
                      · linarith only [h4261, h4787, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4825 | h4825
                      · linarith only [h4, h4825, hlam]
                      · rcases p4722_3 (m.d 1 3) (by simp) with h4827 | h4827
                        · linarith only [h4709, h4827, hlam]
                        · rcases p4722_3 (m.d 2 3) (by simp) with h4829 | h4829
                          · rcases p4722_3 (m.d 3 4) (by simp) with h4830 | h4830
                            · linarith only [h4717, h4830, hlam]
                            · rcases p4722_3 (m.d 3 5) (by simp) with h4832 | h4832
                              · linarith only [h4718, h4832, hlam]
                              · rcases h4bigk with h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c | h4834c
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h3688, h4711, h4717, hc12, hc23, hlam, hphi, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h3688, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4260, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4722_1, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4262, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h2, hlam, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4711, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4715, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h0, h3688, h4717, hc12, hc23, hlam, hphi, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4711, h4717, hc12, hc23, hlam, hphi, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  rcases p4834_3 (m.d 0 4) (by simp) with h4848 | h4848
                                  · linarith only [h3688, h4848, hlam]
                                  · linarith only [h4260, h4848, hlam]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h0, h3688, h4262, h4717, hc12, hc23, hlam, hphi, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4260, hlam, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4713, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4717, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4720, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h0, h3688, hc12, hc45, hlam, hphi, ht23, ht34, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h1, h4711, h4714, h4720, hc12, hc23, hc34, hc45, hlam, hphi, p4722_1, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4719, hlam, p4834_0]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [h4717, h4719, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4834_1]
                                · have p4834_0 := h4834c.1
                                  have p4834_1 := h4834c.2.1
                                  have p4834_2 := h4834c.2.2.1
                                  have p4834_3 := h4834c.2.2.2
                                  linarith only [hlam, p4834_0]
                          · linarith only [h4, h4829, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4863 | h4863
                      · linarith only [h4, h4863, hlam]
                      · linarith only [h1, h4863, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4867 | h4867
                      · linarith only [h4, h4867, hlam]
                      · linarith only [h4260, h4867, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      rcases p4722_3 (m.d 0 3) (by simp) with h4870 | h4870
                      · linarith only [h4, h4870, hlam]
                      · linarith only [h4261, h4870, hlam]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4260, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4713, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4717, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4720, hlam, p4722_1]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4261, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4714, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h4718, hlam, p4722_0]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [h1, h4714, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4722_1]
                    · have p4722_0 := h4722c.1
                      have p4722_1 := h4722c.2.1
                      have p4722_2 := h4722c.2.2.1
                      have p4722_3 := h4722c.2.2.2
                      linarith only [hlam, p4722_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4883 | h4883
                  · linarith only [h0, h3688, h4719, h4883, hc12, hc34, hlam, hphi, ht23]
                  · rcases h3bigk with h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c | h4885c
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h4887 | h4887
                      · rcases p4885_3 (m.d 1 3) (by simp) with h4888 | h4888
                        · linarith only [h1, h4888, hlam]
                        · rcases p4885_3 (m.d 2 3) (by simp) with h4890 | h4890
                          · rcases p4885_3 (m.d 3 4) (by simp) with h4891 | h4891
                            · linarith only [h4260, h4891, hlam]
                            · rcases p4885_3 (m.d 3 5) (by simp) with h4893 | h4893
                              · linarith only [h4261, h4893, hlam]
                              · rcases h4bigk with h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c | h4895c
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h3688, h4719, hc14, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h3688, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h3688, h4719, hc34, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4262, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h2, hlam, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4711, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4715, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4719, hc04, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4719, hc14, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4719, hc34, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4719, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4260, hlam, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4713, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4717, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4883, hlam, p4895_0]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h0, h3688, h4, h4714, h4883, hc12, hc23, hc34, hc45, hlam, hphi, p4885_1, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [h4, h4711, h4714, h4883, hc12, hc23, hc34, hc45, hlam, hphi, p4885_1, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p4895_1]
                                · have p4895_0 := h4895c.1
                                  have p4895_1 := h4895c.2.1
                                  have p4895_2 := h4895c.2.2.1
                                  have p4895_3 := h4895c.2.2.2
                                  linarith only [hlam, p4895_0]
                          · linarith only [h4709, h4890, hlam]
                      · linarith only [h1, h4887, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4, hlam, p4885_1]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h4924 | h4924
                      · rcases p4885_3 (m.d 1 3) (by simp) with h4925 | h4925
                        · linarith only [h1, h4925, hlam]
                        · linarith only [h4713, h4925, hlam]
                      · linarith only [h4924, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h4929 | h4929
                      · rcases p4885_3 (m.d 1 3) (by simp) with h4930 | h4930
                        · linarith only [h1, h4930, hlam]
                        · linarith only [h4714, h4930, hlam]
                      · linarith only [h4929, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h1, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4709, hlam, p4885_1]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h4937 | h4937
                      · rcases p4885_3 (m.d 1 3) (by simp) with h4938 | h4938
                        · rcases p4885_3 (m.d 2 3) (by simp) with h4939 | h4939
                          · rcases p4885_3 (m.d 3 4) (by simp) with h4940 | h4940
                            · linarith only [h4940, hlam, p4885_0]
                            · rcases p4885_3 (m.d 3 5) (by simp) with h4942 | h4942
                              · linarith only [h4714, h4942, hlam]
                              · linarith only [h4883, h4942, hlam]
                          · linarith only [h4717, h4939, hlam]
                        · linarith only [h4938, hlam, p4885_0]
                      · linarith only [h4260, h4937, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h4948 | h4948
                      · rcases p4885_3 (m.d 1 3) (by simp) with h4949 | h4949
                        · rcases p4885_3 (m.d 2 3) (by simp) with h4950 | h4950
                          · rcases p4885_3 (m.d 3 4) (by simp) with h4951 | h4951
                            · linarith only [h4713, h4951, hlam]
                            · rcases p4885_3 (m.d 3 5) (by simp) with h4953 | h4953
                              · linarith only [h4953, hlam, p4885_0]
                              · rcases h4bigk with h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h3688, h4711, hc12, hc24, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h3688, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4262, hc34, hc45, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4262, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h2, hlam, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4711, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4715, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h0, h3688, hc12, hc24, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4711, hc12, hc24, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4719, hc34, hc45, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4719, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4260, hlam, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4713, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4717, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4883, hlam, p4955_0]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h0, h3688, hc12, hc45, hlam, hphi, ht23, ht34, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [h4711, hc12, hc45, hlam, hphi, ht23, ht34, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p4955_1]
                                · have p4955_0 := h4955c.1
                                  have p4955_1 := h4955c.2.1
                                  have p4955_2 := h4955c.2.2.1
                                  have p4955_3 := h4955c.2.2.2
                                  linarith only [hlam, p4955_0]
                          · linarith only [h4718, h4950, hlam]
                        · linarith only [h4949, hlam, p4885_0]
                      · linarith only [h4261, h4948, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h4984 | h4984
                      · linarith only [h4, h4984, hlam]
                      · rcases p4885_3 (m.d 1 3) (by simp) with h4986 | h4986
                        · linarith only [h4709, h4986, hlam]
                        · rcases p4885_3 (m.d 2 3) (by simp) with h4988 | h4988
                          · rcases p4885_3 (m.d 3 4) (by simp) with h4989 | h4989
                            · linarith only [h4717, h4989, hlam]
                            · rcases p4885_3 (m.d 3 5) (by simp) with h4991 | h4991
                              · linarith only [h4718, h4991, hlam]
                              · rcases h4bigk with h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h3688, h4711, hc12, hc24, hlam, hphi, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h3688, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4260, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4885_1, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4262, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h2, hlam, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4711, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4715, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h0, h3688, hc12, hc24, hlam, hphi, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4711, hc12, hc24, hlam, hphi, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4719, hc34, hc45, hlam, hphi, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4719, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4260, hlam, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4713, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4717, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4883, hlam, p4993_0]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h0, h3688, hc12, hc45, hlam, hphi, ht23, ht34, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [h4711, hc12, hc45, hlam, hphi, ht23, ht34, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p4993_1]
                                · have p4993_0 := h4993c.1
                                  have p4993_1 := h4993c.2.1
                                  have p4993_2 := h4993c.2.2.1
                                  have p4993_3 := h4993c.2.2.2
                                  linarith only [hlam, p4993_0]
                          · linarith only [h4, h4988, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h5020 | h5020
                      · linarith only [h4, h5020, hlam]
                      · linarith only [h1, h5020, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h5024 | h5024
                      · linarith only [h4, h5024, hlam]
                      · linarith only [h4260, h5024, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      rcases p4885_3 (m.d 0 3) (by simp) with h5027 | h5027
                      · linarith only [h4, h5027, hlam]
                      · linarith only [h4261, h5027, hlam]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4260, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4713, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4717, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4883, hlam, p4885_1]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4261, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4714, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h4718, hlam, p4885_0]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [h1, h4714, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4885_1]
                    · have p4885_0 := h4885c.1
                      have p4885_1 := h4885c.2.1
                      have p4885_2 := h4885c.2.2.1
                      have p4885_3 := h4885c.2.2.2
                      linarith only [hlam, p4885_0]
              · linarith only [h0, h1, h4, h4714, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h4, h4260, h4717, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5042 | h5042
          · linarith only [h4261, h4262, h4713, h4714, h5042, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5044 | h5044
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5045 | h5045
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5046 | h5046
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5047 | h5047
                  · linarith only [h4261, h4262, h4713, h4714, h5047, hlam]
                  · rcases h3bigk with h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c | h5049c
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      rcases p5049_3 (m.d 0 3) (by simp) with h5051 | h5051
                      · rcases p5049_3 (m.d 1 3) (by simp) with h5052 | h5052
                        · linarith only [h1, h5052, hlam]
                        · rcases p5049_3 (m.d 2 3) (by simp) with h5054 | h5054
                          · rcases p5049_3 (m.d 3 4) (by simp) with h5055 | h5055
                            · linarith only [h4260, h5055, hlam]
                            · rcases p5049_3 (m.d 3 5) (by simp) with h5057 | h5057
                              · linarith only [h4261, h5057, hlam]
                              · linarith only [h4714, h5057, hlam]
                          · linarith only [h4709, h5054, hlam]
                      · linarith only [h1, h5051, hlam]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4, hlam, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4261, h4713, h4714, hlam, p5049_2]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4713, h4714, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h1, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4709, hlam, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4261, h4262, h4714, h5044, h5046, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4714, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4261, h4711, h4713, h4714, hc12, hc23, hlam, hphi, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      rcases p5049_3 (m.d 0 3) (by simp) with h5071 | h5071
                      · linarith only [h4, h5071, hlam]
                      · linarith only [h1, h5071, hlam]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4, h4261, h4713, h4714, hlam, p5049_2]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4713, h4714, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4260, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4713, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h5044, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h5047, hlam, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4261, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h4261, h4713, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5049_1]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [h5045, hlam, p5049_0]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      rcases p5049_3 (m.d 0 3) (by simp) with h5085 | h5085
                      · rcases p5049_3 (m.d 1 3) (by simp) with h5086 | h5086
                        · linarith only [h4714, h5086, hlam]
                        · linarith only [h4713, h5086, hlam]
                      · linarith only [h4260, h5085, hlam]
                    · have p5049_0 := h5049c.1
                      have p5049_1 := h5049c.2.1
                      have p5049_2 := h5049c.2.2.1
                      have p5049_3 := h5049c.2.2.2
                      linarith only [hlam, p5049_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5091 | h5091
                  · linarith only [h1, h4713, h5046, h5091, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h3bigk with h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      rcases p5093_3 (m.d 0 3) (by simp) with h5095 | h5095
                      · rcases p5093_3 (m.d 1 3) (by simp) with h5096 | h5096
                        · linarith only [h1, h5096, hlam]
                        · rcases p5093_3 (m.d 2 3) (by simp) with h5098 | h5098
                          · rcases p5093_3 (m.d 3 4) (by simp) with h5099 | h5099
                            · linarith only [h4260, h5099, hlam]
                            · rcases p5093_3 (m.d 3 5) (by simp) with h5101 | h5101
                              · linarith only [h4261, h5101, hlam]
                              · linarith only [h4714, h5101, hlam]
                          · linarith only [h4709, h5098, hlam]
                      · linarith only [h1, h5095, hlam]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4, hlam, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4261, h4713, h4714, hlam, p5093_2]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4713, h4714, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h1, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4709, hlam, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4, h4261, h4714, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4714, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4261, h4714, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      rcases p5093_3 (m.d 0 3) (by simp) with h5115 | h5115
                      · linarith only [h4, h5115, hlam]
                      · linarith only [h1, h5115, hlam]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4, h4261, h4713, h4714, hlam, p5093_2]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4713, h4714, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4260, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4713, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h5044, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h5091, hlam, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4261, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h4261, h4713, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5093_1]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [h5045, hlam, p5093_0]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      rcases p5093_3 (m.d 0 3) (by simp) with h5129 | h5129
                      · rcases p5093_3 (m.d 1 3) (by simp) with h5130 | h5130
                        · linarith only [h4714, h5130, hlam]
                        · linarith only [h4713, h5130, hlam]
                      · linarith only [h4260, h5129, hlam]
                    · have p5093_0 := h5093c.1
                      have p5093_1 := h5093c.2.1
                      have p5093_2 := h5093c.2.2.1
                      have p5093_3 := h5093c.2.2.2
                      linarith only [hlam, p5093_0]
              · linarith only [h4, h4261, h5045, hlam]
            · linarith only [h1, h4, h4261, h4713, h4714, h5044, hc01, hc15, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5137 | h5137
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5138 | h5138
          · linarith only [h4260, h4262, h4713, h5138, hlam]
          · linarith only [h4713, h5137, h5138, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5141 | h5141
          · linarith only [h2, h4262, h5141, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5143 | h5143
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5144 | h5144
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5145 | h5145
                · linarith only [h4260, h4262, h4709, h4713, h5145, hc12, hc24, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5147 | h5147
                  · linarith only [h0, h3688, h5145, h5147, hc12, hc34, hlam, hphi, ht23]
                  · rcases h3bigk with h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      rcases p5149_3 (m.d 0 3) (by simp) with h5151 | h5151
                      · rcases p5149_3 (m.d 1 3) (by simp) with h5152 | h5152
                        · linarith only [h1, h5152, hlam]
                        · rcases p5149_3 (m.d 2 3) (by simp) with h5154 | h5154
                          · rcases p5149_3 (m.d 3 4) (by simp) with h5155 | h5155
                            · linarith only [h4260, h5155, hlam]
                            · linarith only [h4713, h5155, hlam]
                          · linarith only [h4709, h5154, hlam]
                      · linarith only [h1, h5151, hlam]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4, hlam, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4, h4709, h4713, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4, h4709, h4713, h5147, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h1, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4709, hlam, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4713, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h5137, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4260, h4709, h4713, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      rcases p5149_3 (m.d 0 3) (by simp) with h5169 | h5169
                      · linarith only [h4, h5169, hlam]
                      · linarith only [h1, h5169, hlam]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4709, h4713, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4709, h4713, h5147, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4260, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h3688, h4260, h4709, h5145, hc12, hc45, hlam, hphi, ht23, ht34, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h5143, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h5147, hlam, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4261, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4, h4261, h4709, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h5144, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4, h4261, h4709, h4713, hc12, hc23, hlam, hphi, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
              · linarith only [h4, h4261, h5144, hlam]
            · linarith only [h4, h4260, h5143, hlam]

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4260 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4261 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h4262 | h4262
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x0_x0 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688 h4260 h4261 h4262
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x0_x1 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688 h4260 h4261 h4262

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4260 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4261 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h5187 | h5187
  · linarith only [h4260, h4261, h5187, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5189 | h5189
    · linarith only [h0, h4, h5189, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5191 | h5191
      · linarith only [h0, h3688, h5191, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5193 | h5193
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5194 | h5194
          · linarith only [h1, h4261, h5194, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5196 | h5196
            · linarith only [h2, h5187, h5196, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5198 | h5198
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5199 | h5199
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5200 | h5200
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5201 | h5201
                    · linarith only [h1, h4261, h5193, h5199, h5201, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases h3bigk with h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c | h5203c
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h4261, h5193, h5198, h5200, h5201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h4, hlam, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h4261, h5198, h5200, h5201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h4261, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h1, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5189, hlam, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h1, h4261, h5198, h5200, h5201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5194, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        rcases p5203_3 (m.d 0 3) (by simp) with h5214 | h5214
                        · linarith only [h4, h5214, hlam]
                        · rcases p5203_3 (m.d 1 3) (by simp) with h5216 | h5216
                          · linarith only [h5189, h5216, hlam]
                          · rcases p5203_3 (m.d 2 3) (by simp) with h5218 | h5218
                            · rcases p5203_3 (m.d 3 4) (by simp) with h5219 | h5219
                              · linarith only [h5198, h5219, hlam]
                              · rcases p5203_3 (m.d 3 5) (by simp) with h5221 | h5221
                                · linarith only [h5199, h5221, hlam]
                                · linarith only [h4261, h5221, hlam]
                            · linarith only [h4, h5218, hlam]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        rcases p5203_3 (m.d 0 3) (by simp) with h5225 | h5225
                        · linarith only [h4, h5225, hlam]
                        · linarith only [h1, h5225, hlam]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h4260, h4261, h5198, h5200, h5201, hlam, p5203_2]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h1, h4261, h5193, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h4260, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5193, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5198, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5201, hlam, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h1, h5193, h5199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5193, h5199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5203_1]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [h5199, hlam, p5203_0]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        rcases p5203_3 (m.d 0 3) (by simp) with h5239 | h5239
                        · linarith only [h4261, h5239, hlam]
                        · linarith only [h4260, h5239, hlam]
                      · have p5203_0 := h5203c.1
                        have p5203_1 := h5203c.2.1
                        have p5203_2 := h5203c.2.2.1
                        have p5203_3 := h5203c.2.2.2
                        linarith only [hlam, p5203_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5243 | h5243
                    · linarith only [h1, h5193, h5200, h5243, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h3bigk with h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h4261, h5193, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h4, hlam, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h4261, h5199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h4261, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h1, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5189, hlam, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h1, h4261, h5199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5194, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        rcases p5245_3 (m.d 0 3) (by simp) with h5256 | h5256
                        · linarith only [h4, h5256, hlam]
                        · rcases p5245_3 (m.d 1 3) (by simp) with h5258 | h5258
                          · linarith only [h5189, h5258, hlam]
                          · rcases p5245_3 (m.d 2 3) (by simp) with h5260 | h5260
                            · rcases p5245_3 (m.d 3 4) (by simp) with h5261 | h5261
                              · linarith only [h5198, h5261, hlam]
                              · rcases p5245_3 (m.d 3 5) (by simp) with h5263 | h5263
                                · linarith only [h5199, h5263, hlam]
                                · linarith only [h4261, h5263, hlam]
                            · linarith only [h4, h5260, hlam]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        rcases p5245_3 (m.d 0 3) (by simp) with h5267 | h5267
                        · linarith only [h4, h5267, hlam]
                        · linarith only [h1, h5267, hlam]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h4260, h4261, h5199, hlam, p5245_2]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h0, h4, h4261, hc12, hc23, hlam, hphi, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h4260, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5193, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5198, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5243, hlam, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h1, h5193, h5199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5193, h5199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5245_1]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [h5199, hlam, p5245_0]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        rcases p5245_3 (m.d 0 3) (by simp) with h5281 | h5281
                        · linarith only [h4261, h5281, hlam]
                        · linarith only [h4260, h5281, hlam]
                      · have p5245_0 := h5245c.1
                        have p5245_1 := h5245c.2.1
                        have p5245_2 := h5245c.2.2.1
                        have p5245_3 := h5245c.2.2.2
                        linarith only [hlam, p5245_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5285 | h5285
                  · linarith only [h0, h3688, h5187, h5198, h5199, h5285, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5287 | h5287
                    · linarith only [h1, h5193, h5285, h5287, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h3bigk with h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c | h5289c
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h4, h5199, h5287, hc13, hc45, hlam, hphi, ht34, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h4, hlam, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h4, h5199, h5287, hc34, hc45, hlam, hphi, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h4261, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h1, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5189, hlam, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h1, h4, h5199, h5287, hc34, hc45, hlam, hphi, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5194, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5199, h5287, hc03, hc45, hlam, hphi, ht34, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5199, h5287, hc13, hc45, hlam, hphi, ht34, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5199, h5287, hc34, hc45, hlam, hphi, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5199, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h4260, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5193, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5198, hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [hlam, p5289_0]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5287, hlam, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h1, h5193, h5287, hc34, hc45, hlam, hphi, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h5193, h5287, hc34, hc45, hlam, hphi, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [h0, h4, h5287, hc12, hc45, hlam, hphi, ht23, ht34, p5289_1]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        rcases p5289_3 (m.d 0 3) (by simp) with h5313 | h5313
                        · linarith only [h4261, h5313, hlam]
                        · linarith only [h4260, h5313, hlam]
                      · have p5289_0 := h5289c.1
                        have p5289_1 := h5289c.2.1
                        have p5289_2 := h5289c.2.2.1
                        have p5289_3 := h5289c.2.2.2
                        linarith only [hlam, p5289_0]
              · linarith only [h0, h3, h4, h5193, h5194, h5198, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h4260, h4261, h5193, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4260 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h4261 | h4261
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x0 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688 h4260 h4261
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x1 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688 h4260 h4261

end R2N4
