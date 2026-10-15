import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_64S7

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_13_15_H_I_L_0_L_0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h585 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h783 | h783
  · rcases m.htr 0 1 5 (by decide) (by decide) with h784 | h784
    · rcases m.htr 0 2 3 (by decide) (by decide) with h785 | h785
      · rcases m.htr 0 2 4 (by decide) (by decide) with h786 | h786
        · rcases m.htr 0 2 5 (by decide) (by decide) with h787 | h787
          · rcases m.htr 0 3 4 (by decide) (by decide) with h788 | h788
            · rcases m.htr 0 3 5 (by decide) (by decide) with h789 | h789
              · rcases m.htr 0 4 5 (by decide) (by decide) with h790 | h790
                · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h792 | h792
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h793 | h793
                      · linarith only [h585, h783, h791, h793, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h585, h783, h790, h793, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h788, h792, hc23, hlam, hphi, u3elo0]
                  · linarith only [h585, h783, h788, h791, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h800 | h800
                      · linarith only [h585, h783, h790, h798, h800, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases h0bigk with h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h0, hlam, p802_1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h585, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h585, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p802_1, u3elo1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h585, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p802_1, u3elo1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h784, hc02, hc15, hlam, hphi, ht0b, ht5b, p802_1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h0, h585, h783, h798, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p802_1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          rcases p802_3 (m.d 0 1) (by simp) with h811 | h811
                          · linarith only [h0, h811, hlam]
                          · linarith only [h783, h811, hlam]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          rcases p802_3 (m.d 0 1) (by simp) with h814 | h814
                          · linarith only [h0, h814, hlam]
                          · linarith only [h784, h814, hlam]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h783, h798, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p802_1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h785, hlam, p802_1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h585, h783, h798, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p802_1, u3elo1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h585, h783, h790, h798, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p802_1, u3elo1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h783, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h786, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h788, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h790, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h784, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h787, hlam, p802_1]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h789, hlam, p802_0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [h783, h798, hc34, hlam, hphi, ht45, p802_1, u5elo0]
                        · have p802_0 := h802c.1
                          have p802_1 := h802c.2.1
                          have p802_2 := h802c.2.2.1
                          have p802_3 := h802c.2.2.2
                          linarith only [hlam, p802_0]
                    · linarith only [h585, h783, h798, h799, hc23, hlam, hphi, u3elo1]
                  · linarith only [h585, h798, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h585, h783, h789, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h585, h783, h788, hlam]
          · linarith only [h0, h783, h787, hc14, hlam, hphi, ht45, u5elo2]
        · linarith only [h585, h783, h785, h786, hc23, hlam, hphi, u3elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h838 | h838
        · rcases m.htr 0 2 5 (by decide) (by decide) with h839 | h839
          · rcases m.htr 0 3 4 (by decide) (by decide) with h840 | h840
            · rcases m.htr 0 3 5 (by decide) (by decide) with h841 | h841
              · rcases m.htr 0 4 5 (by decide) (by decide) with h842 | h842
                · rcases m.htr 1 3 4 (by decide) (by decide) with h843 | h843
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h845 | h845
                      · linarith only [h0, h783, h785, h843, h845, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h0, h783, h785, h842, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h0, h785, h844, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h585, h783, h840, h843, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h851 | h851
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h852 | h852
                      · linarith only [h585, h783, h850, h852, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · rcases h0bigk with h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h0, hlam, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h585, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h0, h783, h785, h850, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p854_1, u3elo2]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h0, h785, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p854_1, u3elo2]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h785, hc01, hlam, hphi, ht12, ht23, p854_1, u3elo2]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h785, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h783, h785, h850, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p854_1, u3elo2]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h785, h839, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p854_1, u3elo2]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h585, h783, h850, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p854_1, u3elo1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p854_1, u3elo1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h585, h783, h850, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p854_1, u3elo1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h585, h839, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p854_1, u3elo1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h783, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h838, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h840, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h842, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h784, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h839, hlam, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h841, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h783, h850, hc34, hlam, hphi, ht45, p854_1, u5elo0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                    · linarith only [h783, h842, h850, h851, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h585, h850, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h585, h783, h841, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h0, h783, h785, h840, hlam]
          · linarith only [h0, h783, h839, hc14, hlam, hphi, ht45, u5elo2]
        · linarith only [h0, h783, h838, hlam]
    · linarith only [h783, h784, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h887 | h887
    · rcases m.htr 0 2 3 (by decide) (by decide) with h888 | h888
      · rcases m.htr 0 2 4 (by decide) (by decide) with h889 | h889
        · rcases m.htr 0 2 5 (by decide) (by decide) with h890 | h890
          · rcases m.htr 0 3 4 (by decide) (by decide) with h891 | h891
            · rcases m.htr 0 3 5 (by decide) (by decide) with h892 | h892
              · rcases m.htr 0 4 5 (by decide) (by decide) with h893 | h893
                · rcases m.htr 1 3 4 (by decide) (by decide) with h894 | h894
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h895 | h895
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                      · rcases h0bigk with h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h0, hlam, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h585, hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h783, hlam, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h783, h894, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p897_1, u3elo1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h887, hc02, hc15, hlam, hphi, ht0b, ht5b, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h0, h585, h887, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h0, h783, h887, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          rcases p897_3 (m.d 0 1) (by simp) with h907 | h907
                          · linarith only [h0, h907, hlam]
                          · linarith only [h887, h907, hlam]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h887, hc03, hc15, hlam, hphi, ht0b, ht5b, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h888, hlam, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h585, h889, h895, h896, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p897_1, u3elo1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h585, h892, h896, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p897_1, u3elo1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h887, hc04, hc15, hlam, hphi, ht0b, ht5b, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h889, hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h891, hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h783, h892, h894, h896, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p897_1, u3elo1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h887, hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h890, hlam, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h892, hlam, p897_0]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [h893, hlam, p897_1]
                        · have p897_0 := h897c.1
                          have p897_1 := h897c.2.1
                          have p897_2 := h897c.2.2.1
                          have p897_3 := h897c.2.2.2
                          linarith only [hlam, p897_0]
                      · rcases h0bigk with h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c | h925c
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h585, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h783, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h783, h893, h894, h896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p925_1, u3elo1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, h585, h887, h893, h896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, h893, h896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h0, h893, h896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h887, h893, h896, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h888, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h585, h893, h896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p925_1, u3elo1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h585, h893, h896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p925_1, u3elo1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h887, h893, h896, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h889, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h891, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h783, h893, h894, h896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p925_1, u3elo1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h887, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h890, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h892, hlam, p925_0]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [h893, hlam, p925_1]
                        · have p925_0 := h925c.1
                          have p925_1 := h925c.2.1
                          have p925_2 := h925c.2.2.1
                          have p925_3 := h925c.2.2.2
                          linarith only [hlam, p925_0]
                    · linarith only [h585, h891, h895, hc23, hlam, hphi, u3elo1]
                  · linarith only [h585, h891, h894, hlam]
                · linarith only [h783, h887, h893, hc15, hlam, hphi, u5elo4]
              · linarith only [h585, h887, h892, hc15, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h955 | h955
              · rcases m.htr 0 4 5 (by decide) (by decide) with h956 | h956
                · rcases m.htr 1 3 4 (by decide) (by decide) with h957 | h957
                  · linarith only [h585, h887, h891, h957, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h585, h887, h957, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h585, h887, h891, h956, hc15, hlam, hphi, u5elo4]
              · linarith only [h585, h887, h955, hc15, hlam, hphi, u5elo3]
          · linarith only [h0, h887, h890, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h963 | h963
          · rcases m.htr 0 3 4 (by decide) (by decide) with h964 | h964
            · linarith only [h888, h889, h964, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h966 | h966
              · rcases m.htr 0 4 5 (by decide) (by decide) with h967 | h967
                · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
                  · linarith only [h964, h968, hc03, hlam, hphi, u3elo1]
                  · linarith only [h585, h887, h968, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h888, h889, h967, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h585, h887, h966, hc15, hlam, hphi, u5elo3]
          · linarith only [h888, h963, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h974 | h974
        · rcases m.htr 0 2 5 (by decide) (by decide) with h975 | h975
          · rcases m.htr 0 3 4 (by decide) (by decide) with h976 | h976
            · rcases m.htr 0 3 5 (by decide) (by decide) with h977 | h977
              · rcases m.htr 0 4 5 (by decide) (by decide) with h978 | h978
                · rcases m.htr 1 3 4 (by decide) (by decide) with h979 | h979
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h981 | h981
                      · linarith only [h888, h974, h980, h981, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h888, h974, h978, h981, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h783, h888, h974, h980, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h976, h979, hc13, hlam, hphi, u3elo0]
                · linarith only [h783, h887, h978, hc15, hlam, hphi, u5elo4]
              · linarith only [h783, h887, h888, h974, h977, hc15, hlam, hphi, u5elo3]
            · linarith only [h888, h974, h976, hlam]
          · linarith only [h783, h887, h974, h975, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h990 | h990
          · rcases m.htr 0 3 4 (by decide) (by decide) with h991 | h991
            · rcases m.htr 0 3 5 (by decide) (by decide) with h992 | h992
              · rcases m.htr 0 4 5 (by decide) (by decide) with h993 | h993
                · rcases m.htr 1 3 4 (by decide) (by decide) with h994 | h994
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h995 | h995
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h996 | h996
                      · rcases h0bigk with h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h0, hlam, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h585, hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h783, hlam, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h783, h994, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h974, h995, hc01, hc23, hlam, hphi, ht12, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h888, hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h974, hlam, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h974, h992, h995, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h887, hc03, hc15, hlam, hphi, ht0b, ht5b, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p997_1, u3elo1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h585, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p997_1, u3elo1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h585, h992, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h887, hc04, hc15, hlam, hphi, ht0b, ht5b, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h0, h887, h974, h995, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h991, hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h974, h992, h995, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h887, hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h990, hlam, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h992, hlam, p997_0]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [h993, hlam, p997_1]
                        · have p997_0 := h997c.1
                          have p997_1 := h997c.2.1
                          have p997_2 := h997c.2.2.1
                          have p997_3 := h997c.2.2.2
                          linarith only [hlam, p997_0]
                      · rcases h0bigk with h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h0, hlam, p1023_1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h585, hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h783, hlam, p1023_1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h0, h974, h995, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1023_1, u3elo2]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h974, h995, hc01, hlam, hphi, ht12, ht23, p1023_1, u3elo2]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h888, hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h974, hlam, p1023_1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h974, h993, h995, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1023_1, u3elo2]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h585, h887, h993, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1023_1, u3elo1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1023_1, u3elo1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h585, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1023_1, u3elo1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h585, h993, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1023_1, u3elo1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h887, h993, h996, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1023_1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h0, h783, h887, h993, h994, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1023_1, u3elo1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h991, hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h783, h993, h994, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1023_1, u3elo1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h887, hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h990, hlam, p1023_1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h992, hlam, p1023_0]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [h993, hlam, p1023_1]
                        · have p1023_0 := h1023c.1
                          have p1023_1 := h1023c.2.1
                          have p1023_2 := h1023c.2.2.1
                          have p1023_3 := h1023c.2.2.2
                          linarith only [hlam, p1023_0]
                    · linarith only [h0, h888, h995, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h585, h991, h994, hlam]
                · linarith only [h783, h887, h993, hc15, hlam, hphi, u5elo4]
              · linarith only [h585, h887, h992, hc15, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1053 | h1053
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1054 | h1054
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1055 | h1055
                  · linarith only [h1055, h991, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1055, h585, h887, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h0, h1054, h887, h888, h991, hc15, hlam, hphi, u5elo4]
              · linarith only [h0, h1053, h887, h888, hc15, hlam, hphi, u5elo3]
          · linarith only [h0, h887, h990, hc15, hlam, hphi, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1061 | h1061
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1062 | h1062
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1063 | h1063
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1064 | h1064
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1065 | h1065
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1066 | h1066
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1067 | h1067
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1068 | h1068
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1069 | h1069
                      · rcases h0bigk with h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h0, hlam, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h585, hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h783, hlam, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h887, hlam, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h0, h1061, h1068, h1069, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h0, h1062, h1068, h1069, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h0, h887, hc01, hc12, hlam, hphi, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h585, hc01, hc13, hlam, hphi, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1061, hlam, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1062, h1068, h1069, h585, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1070_1, u3elo1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h585, h887, hc01, hlam, hphi, ht12, ht23, p1070_1, u3elo1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h783, hc01, hc14, hlam, hphi, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1062, hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1064, hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1064, h585, h887, hc01, hlam, hphi, ht12, ht23, p1070_1, u3elo1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1070_1, u5elo0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1063, hlam, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1065, hlam, p1070_0]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [h1066, hlam, p1070_1]
                        · have p1070_0 := h1070c.1
                          have p1070_1 := h1070c.2.1
                          have p1070_2 := h1070c.2.2.1
                          have p1070_3 := h1070c.2.2.2
                          linarith only [hlam, p1070_0]
                      · rcases h0bigk with h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h0, hlam, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h585, hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h783, hlam, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h887, hlam, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h0, h1064, h1066, h1069, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h0, h1066, h1069, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h0, h887, hc01, hc12, hlam, hphi, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h585, hc01, hlam, hphi, ht12, ht23, p1096_1, u3elo1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1061, hlam, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1066, h1069, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1096_1, u3elo1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h585, h887, hc01, hlam, hphi, ht12, ht23, p1096_1, u3elo1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1067, h783, hc01, hlam, hphi, ht12, ht23, p1096_1, u3elo1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1062, hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1064, hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1067, h783, h887, hc01, hlam, hphi, ht12, ht23, p1096_1, u3elo1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1096_1, u5elo0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1063, hlam, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1065, hlam, p1096_0]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [h1066, hlam, p1096_1]
                        · have p1096_0 := h1096c.1
                          have p1096_1 := h1096c.2.1
                          have p1096_2 := h1096c.2.2.1
                          have p1096_3 := h1096c.2.2.2
                          linarith only [hlam, p1096_0]
                    · linarith only [h1064, h1068, h585, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1064, h1067, h585, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1126 | h1126
                      · linarith only [h1062, h1066, h1125, h1126, hlam]
                      · rcases h0bigk with h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c | h1128c
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h0, hlam, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h585, hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h783, hlam, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h887, hlam, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h0, h1065, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h0, h783, hc01, hc12, hlam, hphi, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h0, h887, hc01, hc12, hlam, hphi, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, p1128_1, u3elo0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h1061, hlam, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h585, h783, hc01, hlam, hphi, ht12, ht23, p1128_1, u3elo1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h585, h887, hc01, hlam, hphi, ht12, ht23, p1128_1, u3elo1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h783, hc01, hc14, hlam, hphi, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h1062, hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h1064, hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h1066, hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1128_1, u5elo0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h1063, hlam, p1128_1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h1065, hlam, p1128_0]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [h887, hc04, hlam, hphi, ht45, p1128_1, u5elo1]
                        · have p1128_0 := h1128c.1
                          have p1128_1 := h1128c.2.1
                          have p1128_2 := h1128c.2.2.1
                          have p1128_3 := h1128c.2.2.2
                          linarith only [hlam, p1128_0]
                    · linarith only [h1064, h1125, h585, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1064, h1066, h1124, h585, hc03, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h1064, h1065, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1157 | h1157
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1159 | h1159
                  · linarith only [h1064, h1159, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1159, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1064, h1157, h1158, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1163 | h1163
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1164 | h1164
                  · linarith only [h1064, h1164, h585, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1164, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1167 | h1167
                  · linarith only [h1064, h1167, h585, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1167, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h1061, h1063, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1171 | h1171
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1172 | h1172
            · linarith only [h1061, h1062, h1172, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1174 | h1174
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1175 | h1175
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h1172, h1176, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1176, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1061, h1062, h1175, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
                  · linarith only [h1172, h1181, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1181, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1061, h1062, h1180, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1061, h1171, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1186 | h1186
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1187 | h1187
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1188 | h1188
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1189 | h1189
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1190 | h1190
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1192 | h1192
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1193 | h1193
                      · linarith only [h1061, h1186, h1192, h1193, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · linarith only [h1061, h1186, h1190, h1193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h1061, h1192, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1061, h1186, h1188, h1191, h585, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1200 | h1200
                      · linarith only [h1061, h1186, h1199, h1200, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · rcases h0bigk with h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h0, hlam, p1202_1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h585, hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h783, hlam, p1202_1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h887, hlam, p1202_1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1061, hc01, hlam, hphi, ht12, ht23, p1202_1, u3elo2]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1061, hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1061, h783, hc01, hlam, hphi, ht12, ht23, p1202_1, u3elo2]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1061, h1190, h783, hc01, hlam, hphi, ht12, ht23, p1202_1, u3elo2]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, p1202_1, u3elo0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1202_1, u3elo1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h585, h783, hc01, hlam, hphi, ht12, ht23, p1202_1, u3elo1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1190, h585, h783, hc01, hlam, hphi, ht12, ht23, p1202_1, u3elo1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1190, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1202_1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1186, hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1188, hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1190, hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h887, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1202_1, u5elo1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1187, hlam, p1202_1]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1189, hlam, p1202_0]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [h1061, h1187, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1202_1, u3elo2]
                        · have p1202_0 := h1202c.1
                          have p1202_1 := h1202c.2.1
                          have p1202_2 := h1202c.2.2.1
                          have p1202_3 := h1202c.2.2.2
                          linarith only [hlam, p1202_0]
                    · linarith only [h1061, h1199, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1198, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h1188, h1189, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h1061, h1186, h1188, hlam]
          · linarith only [h1186, h1187, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1233 | h1233
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1234 | h1234
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1235 | h1235
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1238 | h1238
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1239 | h1239
                      · rcases h0bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h0, hlam, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h585, hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h783, hlam, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h887, hlam, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1186, h1238, hc01, hc23, hlam, hphi, ht12, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1061, hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1186, hlam, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1186, h1238, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1240_1, u3elo2]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h585, hc01, hc13, hlam, hphi, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1240_1, u3elo1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h585, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1240_1, u3elo1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h585, h887, hc01, hlam, hphi, ht12, ht23, p1240_1, u3elo1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h783, hc01, hc14, hlam, hphi, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1186, h1233, h1238, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1240_1, u3elo2]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1234, hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1186, h1238, h887, hc01, hlam, hphi, ht12, ht23, p1240_1, u3elo2]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1240_1, u5elo0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1233, hlam, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1235, hlam, p1240_0]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [h1236, hlam, p1240_1]
                        · have p1240_0 := h1240c.1
                          have p1240_1 := h1240c.2.1
                          have p1240_2 := h1240c.2.2.1
                          have p1240_3 := h1240c.2.2.2
                          linarith only [hlam, p1240_0]
                      · rcases h0bigk with h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h585, hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h783, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h887, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1186, h1238, hc01, hlam, hphi, ht12, ht23, p1266_1, u3elo2]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1061, hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1186, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1186, h1236, h1238, h1239, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1266_1, u3elo2]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h585, hc01, hlam, hphi, ht12, ht23, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h585, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1236, h1239, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1237, h783, hc01, hlam, hphi, ht12, ht23, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1233, h1236, h1237, h1239, h783, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1234, hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1236, h1237, h1239, h783, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1266_1, u3elo1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1266_1, u5elo0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1233, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1235, hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1236, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                    · linarith only [h1061, h1238, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1234, h1237, h585, hlam]
                · linarith only [h1186, h1233, h1236, hc25, hlam, hphi, u5elo4]
              · linarith only [h1234, h1235, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1296 | h1296
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1297 | h1297
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1298 | h1298
                  · linarith only [h1061, h1233, h1234, h1298, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1298, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1061, h1233, h1234, h1297, hc25, hlam, hphi, u5elo4]
              · linarith only [h1061, h1233, h1296, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1303 | h1303
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1304 | h1304
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1305 | h1305
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1306 | h1306
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1307 | h1307
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1308 | h1308
                      · rcases h0bigk with h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c | h1309c
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h0, hlam, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h585, hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h783, hlam, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h887, hlam, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1233, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1309_1, u5elo2]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1061, hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1186, hlam, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1233, hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h585, hc01, hc13, hlam, hphi, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1309_1, u3elo1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h0, h1233, h1305, h585, hc01, hlam, hphi, ht12, ht23, p1309_1, u3elo1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h0, h1233, h585, hc01, hlam, hphi, ht12, ht23, p1309_1, u3elo1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h783, hc01, hc14, hlam, hphi, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h0, h1186, hc01, hc24, hlam, hphi, ht12, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1303, hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h0, h1233, h1303, h585, hc01, hlam, hphi, ht12, ht23, p1309_1, u3elo1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1309_1, u5elo0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h0, h887, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1309_1, u5elo1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1304, hlam, p1309_0]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [h1305, hlam, p1309_1]
                        · have p1309_0 := h1309c.1
                          have p1309_1 := h1309c.2.1
                          have p1309_2 := h1309c.2.2.1
                          have p1309_3 := h1309c.2.2.2
                          linarith only [hlam, p1309_0]
                      · rcases h0bigk with h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h0, hlam, p1335_1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h585, hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h783, hlam, p1335_1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h887, hlam, p1335_1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p1335_1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1061, hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1186, hlam, p1335_1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1233, hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h585, hc01, hlam, hphi, ht12, ht23, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1305, h1308, h585, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h585, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1306, h783, hc01, hlam, hphi, ht12, ht23, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h0, h1306, h783, hc01, hlam, hphi, ht12, ht23, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1303, hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h0, h1233, h1306, h783, hc01, hlam, hphi, ht12, ht23, p1335_1, u3elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1335_1, u5elo0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h0, h887, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1335_1, u5elo1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1304, hlam, p1335_0]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [h1305, hlam, p1335_1]
                        · have p1335_0 := h1335c.1
                          have p1335_1 := h1335c.2.1
                          have p1335_2 := h1335c.2.2.1
                          have p1335_3 := h1335c.2.2.2
                          linarith only [hlam, p1335_0]
                    · linarith only [h0, h1061, h1307, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1303, h1306, h585, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1364 | h1364
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1365 | h1365
                      · linarith only [h1303, h1305, h1365, hlam]
                      · rcases h0bigk with h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c | h1367c
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h0, hlam, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h585, hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h783, hlam, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h887, hlam, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1061, hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1186, hlam, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1233, hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h585, hc01, hlam, hphi, ht12, ht23, p1367_1, u3elo1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h585, hc02, hlam, hphi, ht23, p1367_1, u3elo1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h585, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1367_1, u3elo1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h585, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1367_1, u3elo1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h783, hc01, hc14, hlam, hphi, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h0, h1186, hc01, hc24, hlam, hphi, ht12, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1303, hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1305, hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1233, hc01, hc25, hlam, hphi, ht12, p1367_1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h0, h887, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1367_1, u5elo1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h1304, hlam, p1367_0]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [h887, hc04, hlam, hphi, ht45, p1367_1, u5elo1]
                        · have p1367_0 := h1367c.1
                          have p1367_1 := h1367c.2.1
                          have p1367_2 := h1367c.2.2.1
                          have p1367_3 := h1367c.2.2.2
                          linarith only [hlam, p1367_0]
                    · linarith only [h0, h1061, h1364, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1363, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h1303, h1304, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1396 | h1396
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1397 | h1397
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1398 | h1398
                  · linarith only [h1303, h1396, h1398, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1398, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1303, h1396, h1397, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1402 | h1402
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1403 | h1403
                  · linarith only [h0, h1061, h1303, h1403, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1403, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1406 | h1406
                  · linarith only [h0, h1061, h1303, h1406, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1406, h585, hc01, hlam, hphi, ht12, ht23, u3elo3]

theorem r1l7_20_13_15_H_I_L_0_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h585 | h585
  · exact r1l7_20_13_15_H_I_L_0_L_0_x1_x0 m hb0 hb3 hb5 h0 h585
  · exact r1l7_20_13_15_H_I_L_0_L_0_x1_x1 m hb0 hb3 hb5 h0 h585

theorem r1l7_20_13_15_H_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_13_15_H_I_L_0_L_0_x0 m hb0 hb3 hb5 h0
  · exact r1l7_20_13_15_H_I_L_0_L_0_x1 m hb0 hb3 hb5 h0

end R2N4
