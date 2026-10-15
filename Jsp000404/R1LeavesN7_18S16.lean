import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7380000 in
set_option maxHeartbeats 7380000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s8 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h6852 | h6852
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6853 | h6853
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6854 | h6854
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6855 | h6855
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6856 | h6856
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6857 | h6857
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6858 | h6858
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6859 | h6859
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6860 | h6860
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6861 | h6861
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6862 | h6862
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6863 | h6863
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6864 | h6864
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6865 | h6865
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6866 | h6866
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6867 | h6867
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6868 | h6868
                                  · rcases h0bigk with h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c | h6869c
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h0, hlam, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h5743, hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h5743, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h5743, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h0, h5743, h6852, h6861, h6866, h6867, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h0, h6857, h6868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      rcases p6869_3 (m.d 0 1) (by simp) with h6879 | h6879
                                      · linarith only [h0, h6879, hlam]
                                      · linarith only [h6853, h6879, hlam]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6852, h6861, h6865, h6868, hc03, hc45, hlam, hphi, ht0b, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6854, hlam, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h5743, h6852, h6860, h6861, h6865, h6868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      rcases p6869_3 (m.d 0 1) (by simp) with h6886 | h6886
                                      · linarith only [h5743, h6886, hlam]
                                      · linarith only [h6853, h6886, hlam]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6852, hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6855, hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6857, hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h0, h6852, h6853, h6862, h6866, h6868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6853, hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6856, hlam, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6858, hlam, p6869_0]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [h6859, hlam, p6869_1]
                                    · have p6869_0 := h6869c.1
                                      have p6869_1 := h6869c.2.1
                                      have p6869_2 := h6869c.2.2.1
                                      have p6869_3 := h6869c.2.2.2
                                      linarith only [hlam, p6869_0]
                                  · linarith only [h5743, h6852, h6860, h6861, h6867, h6868, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6900 | h6900
                                  · linarith only [h6865, h6867, h6900, hlam]
                                  · rcases h0bigk with h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c | h6902c
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h0, hlam, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h5743, hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h5743, h6860, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h5743, h6859, h6860, h6865, h6867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h0, h5743, h6853, h6862, h6865, h6867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h0, h6859, h6865, h6867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h0, h6859, h6865, h6867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6852, h6859, h6865, h6867, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6854, hlam, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h5743, h6859, h6860, h6865, h6867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h5743, h6859, h6860, h6865, h6867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6852, hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6855, hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6857, hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6852, h6859, h6865, h6867, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6853, hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6856, hlam, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6858, hlam, p6902_0]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [h6859, hlam, p6902_1]
                                    · have p6902_0 := h6902c.1
                                      have p6902_1 := h6902c.2.1
                                      have p6902_2 := h6902c.2.2.1
                                      have p6902_3 := h6902c.2.2.2
                                      linarith only [hlam, p6902_0]
                              · linarith only [h5743, h6853, h6860, h6864, h6865, h6866, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6929 | h6929
                              · linarith only [h5743, h6852, h6860, h6863, h6865, h6929, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6931 | h6931
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6932 | h6932
                                  · rcases h0bigk with h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c | h6933c
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h0, hlam, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h5743, hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h5743, h6860, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h5743, h6860, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h0, h5743, h6852, h6863, h6929, h6932, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h0, h6852, h6863, h6929, h6932, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h0, h6858, h6929, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6852, h6863, h6929, h6932, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6854, hlam, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6852, h6863, h6929, h6932, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h0, h6854, h6858, h6929, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6852, hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6855, hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6857, hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6858, h6929, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6853, hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6856, hlam, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6858, hlam, p6933_0]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [h6859, hlam, p6933_1]
                                    · have p6933_0 := h6933c.1
                                      have p6933_1 := h6933c.2.1
                                      have p6933_2 := h6933c.2.2.1
                                      have p6933_3 := h6933c.2.2.2
                                      linarith only [hlam, p6933_0]
                                  · linarith only [h5743, h6852, h6860, h6861, h6931, h6932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6960 | h6960
                                  · linarith only [h5743, h6852, h6860, h6863, h6865, h6931, h6960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h5743, h6852, h6859, h6860, h6865, h6960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h5743, h6854, h6858, h6864, hc01, hc12, hlam, hphi]
                        · linarith only [h5743, h6857, h6863, hlam]
                      · linarith only [h0, h6856, h6862, hlam]
                    · linarith only [h0, h6855, h6861, hlam]
                  · linarith only [h0, h6854, h6860, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6968 | h6968
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6969 | h6969
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6970 | h6970
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6971 | h6971
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6972 | h6972
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6973 | h6973
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6974 | h6974
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6975 | h6975
                                · linarith only [h0, h6852, h6859, h6969, h6975, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6977 | h6977
                                  · linarith only [h6857, h6859, h6977, hlam]
                                  · rcases h0bigk with h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c | h6979c
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h0, hlam, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h5743, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h5743, h6968, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h5743, h6852, h6859, h6968, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6853, hc02, hc15, hlam, hphi, ht0b, ht5b, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h0, h5743, h6853, h6970, h6973, h6975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      rcases p6979_3 (m.d 0 1) (by simp) with h6988 | h6988
                                      · linarith only [h0, h6988, hlam]
                                      · linarith only [h6852, h6988, hlam]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      rcases p6979_3 (m.d 0 1) (by simp) with h6991 | h6991
                                      · linarith only [h0, h6991, hlam]
                                      · linarith only [h6853, h6991, hlam]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6853, h6970, h6973, h6975, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6854, hlam, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      rcases p6979_3 (m.d 0 1) (by simp) with h6997 | h6997
                                      · linarith only [h5743, h6997, hlam]
                                      · linarith only [h6852, h6997, hlam]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      rcases p6979_3 (m.d 0 1) (by simp) with h7000 | h7000
                                      · linarith only [h5743, h7000, hlam]
                                      · linarith only [h6853, h7000, hlam]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6852, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6855, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6857, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6859, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6853, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6856, hlam, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h6858, hlam, p6979_0]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [h0, h6852, h6853, h6969, h6973, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6979_1]
                                    · have p6979_0 := h6979c.1
                                      have p6979_1 := h6979c.2.1
                                      have p6979_2 := h6979c.2.2.1
                                      have p6979_3 := h6979c.2.2.2
                                      linarith only [hlam, p6979_0]
                              · linarith only [h5743, h6853, h6968, h6972, h6973, h6974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7014 | h7014
                              · linarith only [h5743, h6852, h6968, h6971, h6973, h7014, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7016 | h7016
                                · linarith only [h5743, h6852, h6859, h6968, h6971, h6973, h7016, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7018 | h7018
                                  · linarith only [h6852, h6859, h6971, h7018, hlam]
                                  · rcases h0bigk with h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c | h7020c
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h0, hlam, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h5743, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h5743, h6968, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h5743, h6968, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h0, h6853, h6972, h6973, h7018, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h0, h5743, h6853, h6972, h6973, h7018, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h0, h6857, h6973, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h0, h6853, h6972, h6973, h7018, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6853, h6972, h6973, h7018, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6854, hlam, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6857, h6973, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h0, h6853, h6854, h6972, h6973, h7018, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6852, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6855, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6857, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6859, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6853, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6856, hlam, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6858, hlam, p7020_0]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [h6857, h6973, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7020_1]
                                    · have p7020_0 := h7020c.1
                                      have p7020_1 := h7020c.2.1
                                      have p7020_2 := h7020c.2.2.1
                                      have p7020_3 := h7020c.2.2.2
                                      linarith only [hlam, p7020_0]
                          · linarith only [h5743, h6858, h6972, hlam]
                        · linarith only [h5743, h6857, h6971, hlam]
                      · linarith only [h0, h6856, h6970, hlam]
                    · linarith only [h0, h6855, h6969, hlam]
                  · linarith only [h0, h6854, h6968, hlam]
              · linarith only [h5743, h6853, h6858, hlam]
            · linarith only [h5743, h6852, h6857, hlam]
          · linarith only [h0, h6853, h6856, hlam]
        · linarith only [h5743, h6852, h6854, h6855, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7055 | h7055
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7056 | h7056
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7057 | h7057
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7058 | h7058
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7059 | h7059
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7060 | h7060
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7061 | h7061
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7062 | h7062
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7063 | h7063
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7064 | h7064
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7065 | h7065
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7066 | h7066
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7067 | h7067
                                · linarith only [h0, h6852, h6854, h7060, h7061, h7067, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h6852, h6854, h7059, h7060, h7067, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h6852, h6854, h7058, h7066, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h6852, h6854, h7057, h7065, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h5743, h7058, h7064, hlam]
                        · linarith only [h6854, h7057, h7060, h7063, hlam]
                      · linarith only [h0, h6852, h7056, h7061, h7062, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h6854, h7060, h7061, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7076 | h7076
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7077 | h7077
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7078 | h7078
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7079 | h7079
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7080 | h7080
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7081 | h7081
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7082 | h7082
                                · linarith only [h0, h6852, h7060, h7076, h7082, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h6852, h7059, h7060, h7080, h7082, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h7060, h7081, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h7060, h7080, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h5743, h7058, h7079, hlam]
                        · linarith only [h5743, h7057, h7078, hlam]
                      · linarith only [h0, h6852, h7056, h7076, h7077, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7055, h7076, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7091 | h7091
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7092 | h7092
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7093 | h7093
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7094 | h7094
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7095 | h7095
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7096 | h7096
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7097 | h7097
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7098 | h7098
                                · linarith only [h0, h6852, h6854, h7059, h7091, h7092, h7098, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7100 | h7100
                                  · linarith only [h0, h6853, h6854, h7059, h7091, h7093, h7096, h7098, h7100, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c | h7102c
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h0, hlam, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h5743, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h0, h6854, h7091, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h0, h6854, h7091, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6854, h7091, hc01, hc12, hlam, hphi, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6854, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6852, h6854, h7091, h7092, h7096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6853, h6854, h7091, h7093, h7097, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6852, h6854, h7091, h7092, h7096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6854, h7091, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6852, h6854, h7091, h7092, h7096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6853, h6854, h7091, h7093, h7097, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6852, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h7055, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h7057, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h7059, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h6853, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h7056, hlam, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h7058, hlam, p7102_0]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [h0, h6852, h6853, h7092, h7096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7102_1]
                                    · have p7102_0 := h7102c.1
                                      have p7102_1 := h7102c.2.1
                                      have p7102_2 := h7102c.2.2.1
                                      have p7102_3 := h7102c.2.2.2
                                      linarith only [hlam, p7102_0]
                              · linarith only [h6854, h7058, h7097, hlam]
                            · linarith only [h6854, h7057, h7096, hlam]
                          · linarith only [h6854, h7058, h7091, h7095, hlam]
                        · linarith only [h6854, h7057, h7091, h7094, hlam]
                      · linarith only [h0, h6854, h7091, h7093, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h6854, h7091, h7092, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7134 | h7134
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7135 | h7135
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7136 | h7136
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7137 | h7137
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7138 | h7138
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7139 | h7139
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7140 | h7140
                                · linarith only [h6852, h7059, h7134, h7140, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7142 | h7142
                                  · linarith only [h0, h6853, h7059, h7091, h7135, h7138, h7140, h7142, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases h0bigk with h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c | h7144c
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, hlam, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h5743, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, h7091, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, h7091, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, h7091, hc01, hc23, hlam, hphi, ht12, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h6854, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, h6852, h7091, h7134, h7138, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, h6853, h7091, h7135, h7139, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h5743, h6852, h7091, h7134, h7138, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h5743, h7091, hc02, hc23, hlam, hphi, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      rcases p7144_3 (m.d 0 1) (by simp) with h7158 | h7158
                                      · linarith only [h5743, h7158, hlam]
                                      · linarith only [h6852, h7158, hlam]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      rcases p7144_3 (m.d 0 1) (by simp) with h7161 | h7161
                                      · linarith only [h5743, h7161, hlam]
                                      · linarith only [h6853, h7161, hlam]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h6852, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h7055, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h7057, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h7059, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h6853, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h7056, hlam, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h7058, hlam, p7144_0]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [h0, h6852, h6853, h7091, h7134, h7138, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7144_1]
                                    · have p7144_0 := h7144c.1
                                      have p7144_1 := h7144c.2.1
                                      have p7144_2 := h7144c.2.2.1
                                      have p7144_3 := h7144c.2.2.2
                                      linarith only [hlam, p7144_0]
                              · linarith only [h0, h7091, h7139, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h6852, h7091, h7134, h7138, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h5743, h7058, h7137, hlam]
                        · linarith only [h5743, h6852, h7057, h7059, h7134, h7136, hc24, hc45, hlam, hphi]
                      · linarith only [h0, h6852, h7056, h7134, h7135, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h6852, h7055, h7134, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h6853, h6854, h7058, hlam]
            · linarith only [h0, h6852, h6854, h7057, hlam]
          · linarith only [h0, h6853, h7056, hlam]
        · linarith only [h0, h6852, h7055, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7184 | h7184
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7185 | h7185
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7186 | h7186
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7187 | h7187
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7188 | h7188
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7189 | h7189
                · linarith only [h6852, h6853, h7189, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7191 | h7191
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7192 | h7192
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7193 | h7193
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7194 | h7194
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7195 | h7195
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7196 | h7196
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7197 | h7197
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7198 | h7198
                                · linarith only [h6852, h6853, h7189, h7192, h7198, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7200 | h7200
                                  · linarith only [h6852, h6853, h7184, h7189, h7196, h7200, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h0, hlam, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h5743, hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6852, h6853, h7192, h7196, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6853, hlam, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h0, h5743, h6852, h7192, h7196, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      rcases p7202_3 (m.d 0 1) (by simp) with h7211 | h7211
                                      · linarith only [h0, h7211, hlam]
                                      · linarith only [h6852, h7211, hlam]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h0, h6852, h6853, h7192, h7196, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6852, h7192, h7196, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h7184, hlam, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      rcases p7202_3 (m.d 0 1) (by simp) with h7218 | h7218
                                      · linarith only [h5743, h7218, hlam]
                                      · linarith only [h6852, h7218, hlam]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6852, h6853, h7192, h7196, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6852, hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h7185, hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h7187, hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h7189, hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6852, h7192, h7196, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h7186, hlam, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h7188, hlam, p7202_0]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [h6852, h7189, h7192, h7196, hc34, hc45, hlam, hphi, p7202_1]
                                    · have p7202_0 := h7202c.1
                                      have p7202_1 := h7202c.2.1
                                      have p7202_2 := h7202c.2.2.1
                                      have p7202_3 := h7202c.2.2.2
                                      linarith only [hlam, p7202_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7232 | h7232
                                · linarith only [h6852, h6853, h7189, h7192, h7232, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7234 | h7234
                                  · linarith only [h7188, h7189, h7196, h7197, h7234, hlam]
                                  · rcases h0bigk with h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c | h7236c
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h0, hlam, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h5743, hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h6853, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h6853, hlam, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h0, h5743, hc01, hc12, hlam, hphi, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      rcases p7236_3 (m.d 0 1) (by simp) with h7245 | h7245
                                      · linarith only [h0, h7245, hlam]
                                      · linarith only [h6852, h7245, hlam]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h0, h7188, h7196, h7197, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h6852, h7192, h7196, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h7184, hlam, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      rcases p7236_3 (m.d 0 1) (by simp) with h7252 | h7252
                                      · linarith only [h5743, h7252, hlam]
                                      · linarith only [h6852, h7252, hlam]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h5743, h7188, h7191, h7196, h7197, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h6852, hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h7185, hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h7187, hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h7189, hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h6852, h7192, h7196, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h7186, hlam, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h7188, hlam, p7236_0]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [h6852, h7189, h7192, h7196, hc34, hc45, hlam, hphi, p7236_1]
                                    · have p7236_0 := h7236c.1
                                      have p7236_1 := h7236c.2.1
                                      have p7236_2 := h7236c.2.2.1
                                      have p7236_3 := h7236c.2.2.2
                                      linarith only [hlam, p7236_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7266 | h7266
                              · linarith only [h0, h6852, h7194, h7196, h7266, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7268 | h7268
                                · linarith only [h6852, h6853, h7189, h7194, h7196, h7268, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7270 | h7270
                                  · linarith only [h6852, h6853, h7189, h7194, h7270, hlam]
                                  · rcases h0bigk with h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c | h7272c
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h0, hlam, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h5743, hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h6853, h7191, h7195, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h6853, hlam, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h0, h5743, h6852, h7194, h7196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h0, h6852, h7194, h7196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h0, h6852, h6853, h7194, h7196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h6852, h7194, h7196, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h7184, hlam, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h5743, h6852, h7191, h7194, h7196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h5743, h6852, h6853, h7191, h7194, h7196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h6852, hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h7185, hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h7187, hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h7189, hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h6852, h7194, h7196, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h7186, hlam, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h7188, hlam, p7272_0]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [h6852, h7189, h7194, h7196, hc23, hc45, hlam, hphi, ht34, p7272_1]
                                    · have p7272_0 := h7272c.1
                                      have p7272_1 := h7272c.2.1
                                      have p7272_2 := h7272c.2.2.1
                                      have p7272_3 := h7272c.2.2.2
                                      linarith only [hlam, p7272_0]
                          · linarith only [h5743, h7188, h7195, hlam]
                        · linarith only [h5743, h7187, h7194, hlam]
                      · linarith only [h0, h7186, h7193, hlam]
                    · linarith only [h0, h6852, h7185, h7192, hlam]
                  · linarith only [h0, h7184, h7191, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7303 | h7303
                · linarith only [h5743, h6852, h7188, h7303, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7305 | h7305
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7306 | h7306
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7307 | h7307
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7308 | h7308
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7309 | h7309
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7310 | h7310
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7311 | h7311
                              · linarith only [h5743, h6852, h7184, h7188, h7306, h7310, h7311, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7313 | h7313
                                · linarith only [h5743, h6852, h7188, h7303, h7306, h7309, h7313, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7315 | h7315
                                  · linarith only [h5743, h6852, h7188, h7303, h7306, h7310, h7315, hlam]
                                  · rcases h0bigk with h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c | h7317c
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h0, hlam, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h5743, hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h5743, h7188, h7305, h7309, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h6853, hlam, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h0, h5743, h6852, h7306, h7310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      rcases p7317_3 (m.d 0 1) (by simp) with h7326 | h7326
                                      · linarith only [h0, h7326, hlam]
                                      · linarith only [h6852, h7326, hlam]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h0, h5743, h6852, h7188, h7306, h7310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h6852, h7306, h7310, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7184, hlam, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h6852, h7188, h7305, h7306, h7309, h7310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7188, hlam, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h6852, hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7185, hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7187, hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7303, hlam, p7317_0]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h6852, h6853, h7305, h7306, h7309, h7310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7186, hlam, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h7188, h7305, h7309, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [h6852, h7188, h7305, h7306, h7309, h7310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7317_1]
                                    · have p7317_0 := h7317c.1
                                      have p7317_1 := h7317c.2.1
                                      have p7317_2 := h7317c.2.2.1
                                      have p7317_3 := h7317c.2.2.2
                                      linarith only [hlam, p7317_0]
                            · linarith only [h7187, h7188, h7305, h7309, h7310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7346 | h7346
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7347 | h7347
                              · linarith only [h5743, h7309, h7347, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7349 | h7349
                                · linarith only [h5743, h6852, h7306, h7309, h7349, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7351 | h7351
                                  · linarith only [h5743, h6852, h7188, h7303, h7306, h7309, h7346, h7351, hc03, hc35, hlam, hphi]
                                  · linarith only [h5743, h6852, h7309, h7351, hc14, hc45, hlam, hphi]
                            · linarith only [h5743, h7187, h7309, h7346, hc23, hc35, hlam, hphi]
                        · linarith only [h5743, h6852, h7187, h7308, hlam]
                      · linarith only [h0, h7186, h7307, hlam]
                    · linarith only [h0, h7185, h7306, hlam]
                  · linarith only [h0, h7184, h7305, hlam]
            · linarith only [h5743, h6852, h7187, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7360 | h7360
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7361 | h7361
              · linarith only [h7184, h7186, h7361, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7363 | h7363
                · linarith only [h0, h6852, h7186, h7363, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7365 | h7365
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7366 | h7366
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7367 | h7367
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7368 | h7368
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7369 | h7369
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7370 | h7370
                            · linarith only [h7184, h7186, h7367, h7370, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h7184, h7186, h7360, h7367, h7370, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7373 | h7373
                            · linarith only [h7184, h7186, h7367, h7373, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h7184, h7186, h7360, h7367, h7373, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h5743, h7184, h7186, h7360, h7367, h7368, hc01, hc12, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7377 | h7377
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7378 | h7378
                          · linarith only [h5743, h6852, h7361, h7365, h7366, h7367, h7378, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7380 | h7380
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7381 | h7381
                              · linarith only [h5743, h6852, h7366, h7378, h7380, h7381, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7383 | h7383
                                · linarith only [h0, h6852, h7363, h7366, h7367, h7381, h7383, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h5743, h6852, h7365, h7367, h7383, hc14, hc45, hlam, hphi]
                            · linarith only [h5743, h7360, h7378, h7380, hc23, hc35, hlam, hphi]
                        · linarith only [h5743, h6852, h7360, h7377, hlam]
                    · linarith only [h0, h7185, h7366, hlam]
                  · linarith only [h0, h7184, h7365, hlam]
            · linarith only [h5743, h6852, h7360, hlam]
        · linarith only [h0, h6852, h7185, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7392 | h7392
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7393 | h7393
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7394 | h7394
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7395 | h7395
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7396 | h7396
                · linarith only [h6852, h6853, h7396, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7398 | h7398
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7399 | h7399
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7400 | h7400
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7401 | h7401
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7402 | h7402
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7403 | h7403
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7404 | h7404
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7405 | h7405
                                · linarith only [h6852, h6853, h7184, h7393, h7396, h7398, h7399, h7405, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7407 | h7407
                                  · linarith only [h6852, h6853, h7396, h7399, h7403, h7407, hlam]
                                  · rcases h0bigk with h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c | h7409c
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h0, hlam, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h5743, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6853, h7184, h7393, h7398, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6853, hlam, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7184, h7398, hc01, hc12, hlam, hphi, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7184, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, h7184, h7398, h7399, h7403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7184, h7398, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, h7399, h7403, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7184, h7398, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, h7184, h7398, h7399, h7403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, h6853, h7184, h7398, h7399, h7403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7392, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7394, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7396, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, h7393, h7399, h7403, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7393, hlam, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h7395, hlam, p7409_0]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [h6852, h7184, h7393, h7398, h7399, h7403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7409_1]
                                    · have p7409_0 := h7409c.1
                                      have p7409_1 := h7409c.2.1
                                      have p7409_2 := h7409c.2.2.1
                                      have p7409_3 := h7409c.2.2.2
                                      linarith only [hlam, p7409_0]
                              · linarith only [h7184, h7395, h7404, hlam]
                            · linarith only [h7184, h7394, h7403, hlam]
                          · linarith only [h7184, h7393, h7395, h7398, h7402, hlam]
                        · linarith only [h7184, h7394, h7398, h7401, hlam]
                      · linarith only [h6853, h7184, h7393, h7398, h7400, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h6852, h6853, h7184, h7393, h7398, h7399, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7441 | h7441
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7442 | h7442
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7443 | h7443
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7444 | h7444
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7445 | h7445
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7446 | h7446
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7447 | h7447
                                · linarith only [h6852, h6853, h7398, h7441, h7442, h7447, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7449 | h7449
                                  · linarith only [h6852, h6853, h7396, h7441, h7445, h7449, hlam]
                                  · rcases h0bigk with h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c | h7451c
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h0, hlam, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h5743, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h6853, h7398, h7442, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h6853, hlam, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7184, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h0, h6852, h7398, h7441, h7445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h0, h6852, h6853, h7398, h7441, h7445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h6852, h7184, h7441, h7445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7184, hc02, hc23, hlam, hphi, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      rcases p7451_3 (m.d 0 1) (by simp) with h7465 | h7465
                                      · linarith only [h5743, h7465, hlam]
                                      · linarith only [h6852, h7465, hlam]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h5743, h6852, h6853, h7398, h7441, h7445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h6852, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7392, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7394, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7396, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h6852, h7393, h7441, h7445, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7393, hlam, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h7395, hlam, p7451_0]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [h0, h6852, h7393, h7398, h7441, h7445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7451_1]
                                    · have p7451_0 := h7451c.1
                                      have p7451_1 := h7451c.2.1
                                      have p7451_2 := h7451c.2.2.1
                                      have p7451_3 := h7451c.2.2.2
                                      linarith only [hlam, p7451_0]
                              · linarith only [h0, h6852, h7398, h7441, h7445, h7446, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h6852, h6853, h7398, h7442, h7443, h7445, hlam]
                          · linarith only [h0, h5743, h6852, h7393, h7395, h7398, h7441, h7444, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h5743, h7394, h7443, hlam]
                      · linarith only [h0, h6852, h7393, h7441, h7442, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7392, h7441, hlam]
              · linarith only [h7184, h7393, h7395, hlam]
            · linarith only [h0, h6852, h7184, h7394, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7487 | h7487
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7488 | h7488
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7489 | h7489
                · linarith only [h0, h6852, h7393, h7489, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7491 | h7491
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7492 | h7492
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7493 | h7493
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7494 | h7494
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7495 | h7495
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7496 | h7496
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7497 | h7497
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7498 | h7498
                                · linarith only [h0, h6852, h7393, h7489, h7491, h7492, h7497, h7498, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7500 | h7500
                                  · linarith only [h0, h6852, h7393, h7492, h7496, h7498, h7500, hlam]
                                  · rcases h0bigk with h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c | h7502c
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h0, hlam, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h5743, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h0, h7393, h7491, h7497, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6853, hlam, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7393, h7491, h7497, hc01, hc12, hlam, hphi, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7184, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6852, h7393, h7491, h7492, h7496, h7497, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7393, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6852, h7492, h7496, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7184, h7491, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6852, h7184, h7491, h7492, h7496, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h0, h6852, h7184, h7393, h7491, h7492, h7496, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6852, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7392, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7487, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7489, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6852, h7492, h7496, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h0, h6852, h7393, h7491, h7492, h7496, h7497, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h7488, hlam, p7502_0]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [h6852, h7393, h7491, h7492, h7496, h7497, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7502_1]
                                    · have p7502_0 := h7502c.1
                                      have p7502_1 := h7502c.2.1
                                      have p7502_2 := h7502c.2.2.1
                                      have p7502_3 := h7502c.2.2.2
                                      linarith only [hlam, p7502_0]
                              · linarith only [h7184, h7488, h7497, hlam]
                            · linarith only [h7184, h7487, h7496, hlam]
                          · linarith only [h5743, h6852, h7488, h7492, h7495, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h7184, h7487, h7491, h7494, hlam]
                      · linarith only [h0, h6852, h7184, h7491, h7492, h7493, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h6852, h7184, h7491, h7492, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7534 | h7534
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7535 | h7535
                      · linarith only [h0, h6852, h7393, h7491, h7534, h7535, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7537 | h7537
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7538 | h7538
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7539 | h7539
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7540 | h7540
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7541 | h7541
                                · linarith only [h0, h6852, h7534, h7535, h7540, h7541, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h6852, h7534, h7535, h7539, h7541, hc34, hc45, hlam, hphi]
                              · linarith only [h5743, h7488, h7491, h7540, hlam]
                            · linarith only [h0, h7491, h7539, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h5743, h7488, h7538, hlam]
                        · linarith only [h5743, h7487, h7537, hlam]
                    · linarith only [h0, h6852, h7392, h7534, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7549 | h7549
                · linarith only [h6852, h6853, h7549, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7551 | h7551
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7552 | h7552
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7553 | h7553
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7554 | h7554
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7555 | h7555
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7556 | h7556
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7557 | h7557
                              · linarith only [h0, h6852, h7184, h7488, h7551, h7552, h7556, h7557, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h6852, h7184, h7551, h7552, h7555, h7556, h7557, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h6852, h7184, h7487, h7552, h7556, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7561 | h7561
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7562 | h7562
                              · linarith only [h5743, h6852, h7552, h7555, h7561, h7562, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7564 | h7564
                                · linarith only [h0, h6852, h7184, h7549, h7551, h7552, h7564, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7566 | h7566
                                  · linarith only [h0, h6852, h7184, h7551, h7552, h7555, h7561, h7564, h7566, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · linarith only [h0, h6852, h7184, h7551, h7555, h7566, hc14, hc45, hlam, hphi]
                            · linarith only [h0, h6852, h7184, h7487, h7552, h7561, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h5743, h6852, h7487, h7554, hlam]
                      · linarith only [h0, h7184, h7551, h7553, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h6852, h7184, h7551, h7552, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7573 | h7573
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7574 | h7574
                      · linarith only [h0, h6852, h7393, h7551, h7573, h7574, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7576 | h7576
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7577 | h7577
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7578 | h7578
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7579 | h7579
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7580 | h7580
                                · linarith only [h0, h6852, h7573, h7574, h7580, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h6852, h7573, h7574, h7578, h7580, hc34, hc45, hlam, hphi]
                              · linarith only [h7551, h7577, h7579, hlam]
                            · linarith only [h0, h6852, h7184, h7488, h7551, h7573, h7577, h7578, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7585 | h7585
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7586 | h7586
                              · linarith only [h0, h6852, h7551, h7573, h7577, h7585, h7586, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h6852, h7551, h7573, h7585, h7586, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h6852, h7551, h7573, h7585, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h6852, h7487, h7551, h7573, h7576, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7392, h7573, hlam]
            · linarith only [h5743, h6852, h7487, hlam]
        · linarith only [h0, h6852, h7392, hlam]
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9 m hb0 hb2 hb3 hb5 h0 h5743 h6852

end R2N4
