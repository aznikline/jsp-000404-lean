import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S7

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_0_H_I_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h829 | h829
  · rcases m.htr 0 2 4 (by decide) (by decide) with h830 | h830
    · rcases m.htr 0 2 5 (by decide) (by decide) with h831 | h831
      · rcases m.htr 0 3 4 (by decide) (by decide) with h832 | h832
        · rcases m.htr 0 4 5 (by decide) (by decide) with h833 | h833
          · rcases m.htr 1 2 4 (by decide) (by decide) with h834 | h834
            · rcases m.htr 1 2 5 (by decide) (by decide) with h835 | h835
              · rcases m.htr 1 4 5 (by decide) (by decide) with h836 | h836
                · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h839 | h839
                      · linarith only [h829, h837, h839, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · linarith only [h834, h838, h839, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                      · linarith only [h829, h832, h838, h842, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases h4bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h0, hlam, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h830, h837, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h829, h832, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h829, h832, h837, h838, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h834, h837, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h834, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h834, h837, h838, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h830, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h834, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h833, h838, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h838, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h832, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h0, h833, h838, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h837, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h842, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h833, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h836, hlam, p844_0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h833, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p844_1]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [h829, h832, h833, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p844_1, u2elo0]
                        · have p844_0 := h844c.1
                          have p844_1 := h844c.2.1
                          have p844_2 := h844c.2.2.1
                          have p844_3 := h844c.2.2.2
                          linarith only [hlam, p844_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h870 | h870
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h871 | h871
                      · rcases h4bigk with h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h0, hlam, p872_1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h829, h832, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p872_1, u2elo0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h829, h832, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p872_1, u2elo0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h829, h832, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p872_1, u2elo0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h834, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p872_1, u2elo1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h834, h870, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p872_1, u2elo1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h834, h837, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p872_1, u2elo1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h834, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p872_1, u2elo1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h830, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h834, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h837, hlam, p872_1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p872_1, u2elo3]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h832, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h0, h832, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p872_1]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h829, h832, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p872_1, u2elo0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h829, h832, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p872_1, u2elo0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h833, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h836, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h870, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [h871, hlam, p872_0]
                        · have p872_0 := h872c.1
                          have p872_1 := h872c.2.1
                          have p872_2 := h872c.2.2.1
                          have p872_3 := h872c.2.2.2
                          linarith only [hlam, p872_0]
                      · linarith only [h837, h870, h871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h899 | h899
                      · linarith only [h829, h832, h870, h899, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h829, h832, h833, h837, h899, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h0, h829, h832, h833, h836, hc01, hlam, hphi, ht12, u2elo0]
              · linarith only [h831, h835, hc12, hlam, hphi, u2elo0]
            · linarith only [h830, h834, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h905 | h905
            · rcases m.htr 1 2 5 (by decide) (by decide) with h906 | h906
              · rcases m.htr 1 4 5 (by decide) (by decide) with h907 | h907
                · linarith only [h0, h833, h905, h907, hc01, hlam, hphi, ht12, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h909 | h909
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h910 | h910
                    · linarith only [h0, h907, h910, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h912 | h912
                      · linarith only [h0, h907, h912, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h4bigk with h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c | h914c
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h0, hlam, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h0, h907, hc24, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h0, h907, hc34, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h833, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h907, hc04, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h907, hc24, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h907, hc34, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h907, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h830, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h905, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p914_1, u2elo3]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h910, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h832, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h909, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h912, hlam, p914_0]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hc04, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [h909, hc34, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hc34, hc45, hlam, hphi, p914_1]
                        · have p914_0 := h914c.1
                          have p914_1 := h914c.2.1
                          have p914_2 := h914c.2.2.1
                          have p914_3 := h914c.2.2.2
                          linarith only [hlam, p914_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h940 | h940
                    · linarith only [h832, h833, h909, h940, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h942 | h942
                      · linarith only [h0, h832, h907, h942, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h4bigk with h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h0, hlam, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h0, h907, hc24, hc45, hlam, hphi, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h0, h907, h909, hc23, hc45, hlam, hphi, ht34, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h833, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h907, hc04, hc45, hlam, hphi, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h907, hc24, hc45, hlam, hphi, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h907, h909, hc23, hc45, hlam, hphi, ht34, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h907, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h830, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h905, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h909, hlam, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h940, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h832, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h829, h832, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p944_1, u2elo0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h829, h832, h909, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p944_1, u2elo0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h942, hlam, p944_0]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [hc04, hc45, hlam, hphi, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h909, hc23, hc45, hlam, hphi, ht34, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [h909, hc23, hc45, hlam, hphi, ht34, p944_1]
                        · have p944_0 := h944c.1
                          have p944_1 := h944c.2.1
                          have p944_2 := h944c.2.2.1
                          have p944_3 := h944c.2.2.2
                          linarith only [hlam, p944_0]
              · linarith only [h831, h906, hc12, hlam, hphi, u2elo0]
            · linarith only [h830, h905, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h972 | h972
          · rcases m.htr 1 2 4 (by decide) (by decide) with h973 | h973
            · rcases m.htr 1 2 5 (by decide) (by decide) with h974 | h974
              · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                · rcases m.htr 2 3 4 (by decide) (by decide) with h976 | h976
                  · linarith only [h829, h832, h976, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h979 | h979
                      · rcases h4bigk with h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c | h980c
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h0, hlam, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h832, h978, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h832, hlam, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h830, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p980_1, u2elo0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h973, h978, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p980_1, u2elo1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h973, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p980_1, u2elo1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h973, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p980_1, u2elo1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h830, hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h973, hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h976, hlam, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p980_1, u2elo3]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h978, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p980_1]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          rcases p980_3 (m.d 0 4) (by simp) with h1000 | h1000
                          · linarith only [h1000, h832, hlam]
                          · linarith only [h1000, h972, hlam]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h972, hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h975, hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h978, hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [h979, hlam, p980_0]
                        · have p980_0 := h980c.1
                          have p980_1 := h980c.2.1
                          have p980_2 := h980c.2.2.1
                          have p980_3 := h980c.2.2.2
                          linarith only [hlam, p980_0]
                      · linarith only [h830, h978, h979, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1009 | h1009
                      · rcases h4bigk with h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c | h1010c
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h0, hlam, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h832, h976, hc23, hc34, hlam, hphi, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h832, hlam, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h830, h976, h978, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1010_1, u2elo0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h973, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1010_1, u2elo1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h973, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1010_1, u2elo1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h973, h976, h978, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1010_1, u2elo1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h830, hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h973, hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h976, hlam, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h978, hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h972, h976, h978, hc23, hc34, hlam, hphi, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h976, hc23, hc34, hlam, hphi, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h976, h978, hc23, hc34, hlam, hphi, p1010_1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h972, hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h975, hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h0, h972, h973, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1010_1, u2elo1]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [h1009, hlam, p1010_0]
                        · have p1010_0 := h1010c.1
                          have p1010_1 := h1010c.2.1
                          have p1010_2 := h1010c.2.2.1
                          have p1010_3 := h1010c.2.2.2
                          linarith only [hlam, p1010_0]
                      · linarith only [h0, h1009, h829, h832, h972, h973, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h972, h975, hlam]
              · linarith only [h0, h973, h974, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h830, h973, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1040 | h1040
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1041 | h1041
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1042 | h1042
                · linarith only [h0, h1040, h1042, h972, hc01, hlam, hphi, ht12, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1044 | h1044
                  · linarith only [h1044, h829, h832, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1046 | h1046
                    · linarith only [h0, h1042, h1046, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1048 | h1048
                      · linarith only [h0, h1042, h1048, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h4bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, h1042, hc24, hc45, hlam, hphi, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h832, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h972, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1042, hc04, hc45, hlam, hphi, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1042, hc24, hc45, hlam, hphi, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1042, hc34, hc45, hlam, hphi, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1042, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h830, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1040, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1044, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1046, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1048, hc14, hc45, hlam, hphi, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1044, h1048, hc23, hc45, hlam, hphi, ht34, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1048, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1044, hc23, hc45, hlam, hphi, ht34, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hc34, hc45, hlam, hphi, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
              · linarith only [h1041, h831, hc12, hlam, hphi, u2elo0]
            · linarith only [h1040, h830, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1078 | h1078
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1079 | h1079
          · linarith only [h1079, h830, h831, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1081 | h1081
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1082 | h1082
              · linarith only [h1082, h829, h831, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · linarith only [h0, h1081, h1082, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h1081, h830, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
          · linarith only [h1086, h830, h831, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1089 | h1089
              · linarith only [h1089, h831, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1088, h1089, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h1088, h830, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1093 | h1093
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1094 | h1094
        · linarith only [h1094, h829, h830, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1096 | h1096
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1097 | h1097
            · linarith only [h1097, h830, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1099 | h1099
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1100 | h1100
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1101 | h1101
                  · linarith only [h1094, h1101, h829, h830, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1103 | h1103
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1104 | h1104
                      · rcases h4bigk with h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h0, hlam, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h830, hlam, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1094, hlam, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h830, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1, u2elo3]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1097, hlam, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1097, h1101, hlam, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1097, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1, u2elo3]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h830, hc02, hlam, hphi, p1105_1, u2elo3]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1105_1, u2elo3]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1101, hlam, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1, u2elo3]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h829, h830, hc23, hc34, hlam, hphi, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1097, hc12, hc34, hlam, hphi, ht23, p1105_1]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          rcases p1105_3 (m.d 0 4) (by simp) with h1125 | h1125
                          · linarith only [h1094, h1125, hlam]
                          · linarith only [h1096, h1125, hlam]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1096, hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1100, hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1103, hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [h1104, hlam, p1105_0]
                        · have p1105_0 := h1105c.1
                          have p1105_1 := h1105c.2.1
                          have p1105_2 := h1105c.2.2.1
                          have p1105_3 := h1105c.2.2.2
                          linarith only [hlam, p1105_0]
                      · linarith only [h1093, h1103, h1104, h830, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h1103, h829, h830, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1096, h1100, hlam]
              · linarith only [h1093, h1099, hc12, hlam, hphi, u2elo0]
          · linarith only [h1093, h1096, h830, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1138 | h1138
        · linarith only [h1138, h829, h830, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1140 | h1140
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1141 | h1141
            · linarith only [h1141, h830, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1143 | h1143
              · linarith only [h1093, h1141, h1143, h829, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1145 | h1145
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1146 | h1146
                  · linarith only [h1138, h1146, h829, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1148 | h1148
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1149 | h1149
                      · rcases h4bigk with h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h0, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h830, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1138, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h830, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1150_1, u2elo3]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1141, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1141, h1146, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1141, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1150_1, u2elo3]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1093, h1140, hc02, hlam, hphi, p1150_1, u2elo3]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1150_1, u2elo3]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1146, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1150_1, u2elo3]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1093, h1140, h829, hc23, hc34, hlam, hphi, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1093, h1148, h829, hc23, hc34, hlam, hphi, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          rcases p1150_3 (m.d 0 4) (by simp) with h1170 | h1170
                          · linarith only [h1138, h1170, hlam]
                          · linarith only [h1140, h1170, hlam]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1140, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1145, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1148, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1149, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                      · linarith only [h1138, h1140, h1149, hlam]
                    · linarith only [h0, h1140, h1148, h829, h830, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1140, h1145, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1181 | h1181
            · linarith only [h1181, h829, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1183 | h1183
              · linarith only [h1093, h1181, h1183, h829, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1185 | h1185
                · linarith only [h0, h1140, h1181, h1185, hc01, hlam, hphi, ht12, u2elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1187 | h1187
                  · linarith only [h0, h1185, h1187, h829, h830, hc34, hc45, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1189 | h1189
                    · linarith only [h0, h1185, h1189, h830, hc02, hlam, hphi, u2elo3]
                    · linarith only [h1189, h829, h830, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1192 | h1192
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1193 | h1193
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1194 | h1194
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1195 | h1195
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1196 | h1196
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1197 | h1197
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1200 | h1200
                    · linarith only [h1192, h1200, h829, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h1192, h1195, h1200, h829, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1193, h1194, h1199, h829, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h1192, h1195, h1198, hc01, hlam, hphi, ht12, u2elo0]
              · linarith only [h0, h1196, h1197, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h1192, h1196, h829, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1207 | h1207
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1209 | h1209
                · linarith only [h0, h1195, h1207, h1209, hc01, hlam, hphi, ht12, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1211 | h1211
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1212 | h1212
                    · linarith only [h1192, h1212, h829, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1214 | h1214
                      · linarith only [h0, h1193, h1209, h1211, h1212, h1214, h829, hc01, hlam, hphi, ht12, u2elo2]
                      · rcases h4bigk with h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h0, hlam, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h0, h1209, h1211, hc34, hc45, hlam, hphi, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1192, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1216_1, u2elo2]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1195, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1209, hc04, hc45, hlam, hphi, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1209, hc24, hc45, hlam, hphi, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1209, hc34, hc45, hlam, hphi, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1209, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1192, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1207, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1216_1, u2elo3]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1212, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1194, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1211, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1214, hlam, p1216_0]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [h1211, hc34, hc45, hlam, hphi, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hc34, hc45, hlam, hphi, p1216_1]
                        · have p1216_0 := h1216c.1
                          have p1216_1 := h1216c.2.1
                          have p1216_2 := h1216c.2.2.1
                          have p1216_3 := h1216c.2.2.2
                          linarith only [hlam, p1216_0]
                  · linarith only [h1194, h1211, h829, hlam]
              · linarith only [h1193, h1208, h829, hc12, hlam, hphi, u2elo2]
            · linarith only [h1192, h1207, h829, hc12, hlam, hphi, u2elo2]
        · linarith only [h1192, h1194, h829, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1246 | h1246
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1247 | h1247
          · linarith only [h1192, h1193, h1247, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1249 | h1249
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1250 | h1250
              · linarith only [h1193, h1250, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1249, h1250, hc01, hlam, hphi, ht12, u2elo4]
            · linarith only [h1192, h1249, hc12, hlam, hphi, u2elo0]
        · linarith only [h1192, h1246, h829, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1255 | h1255
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1256 | h1256
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1257 | h1257
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1258 | h1258
            · linarith only [h1192, h1258, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1260 | h1260
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1261 | h1261
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1262 | h1262
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1263 | h1263
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1264 | h1264
                      · rcases h4bigk with h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c | h1265c
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h0, hlam, p1265_1]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1192, hlam, p1265_1]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1264, hc04, hc45, hlam, hphi, ht0b, ht5b, p1265_1]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1192, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo3]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1265_1]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1258, hlam, p1265_1]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1258, h1262, h1264, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1258, h1262, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1192, h1255, h1262, h1263, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1262, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1262, h1264, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1262, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1256, hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h0, h1256, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1265_1]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1262, hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1256, h829, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1265_1, u2elo2]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1257, hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1261, hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1263, hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [h1264, hlam, p1265_0]
                        · have p1265_0 := h1265c.1
                          have p1265_1 := h1265c.2.1
                          have p1265_2 := h1265c.2.2.1
                          have p1265_3 := h1265c.2.2.2
                          linarith only [hlam, p1265_0]
                      · linarith only [h1255, h1263, h1264, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h1192, h1257, h1263, hlam]
                  · linarith only [h1256, h1262, h829, hlam]
                · linarith only [h0, h1255, h1257, h1261, h829, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1255, h1260, h829, hc12, hlam, hphi, u2elo2]
          · linarith only [h1192, h1255, h1257, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1297 | h1297
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1298 | h1298
            · linarith only [h1192, h1298, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1300 | h1300
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1301 | h1301
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1302 | h1302
                  · linarith only [h1255, h1256, h1302, h829, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1304 | h1304
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1305 | h1305
                      · rcases h4bigk with h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h0, hlam, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1192, hlam, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1256, hlam, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1192, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1306_1, u2elo3]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1298, hlam, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1298, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1306_1, u2elo3]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1298, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1306_1, u2elo3]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1255, h1256, h1304, h829, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1306_1, u2elo3]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1306_1, u2elo3]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1302, hlam, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1306_1, u2elo3]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1255, h1256, h1304, h829, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1192, h1255, h1304, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1306_1]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          rcases p1306_3 (m.d 0 4) (by simp) with h1326 | h1326
                          · linarith only [h1256, h1326, hlam]
                          · linarith only [h1297, h1326, hlam]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1297, hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1301, hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1304, hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [h1305, hlam, p1306_0]
                        · have p1306_0 := h1306c.1
                          have p1306_1 := h1306c.2.1
                          have p1306_2 := h1306c.2.2.1
                          have p1306_3 := h1306c.2.2.2
                          linarith only [hlam, p1306_0]
                      · linarith only [h1255, h1304, h1305, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h1255, h1297, h1302, h1304, h829, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h1255, h1297, h1301, h829, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1255, h1300, h829, hc12, hlam, hphi, u2elo2]
          · linarith only [h1255, h1256, h1297, h829, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1339 | h1339
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1340 | h1340
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
            · linarith only [h1192, h1341, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1343 | h1343
              · linarith only [h1255, h1341, h1343, hc02, hlam, hphi, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1345 | h1345
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1347 | h1347
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1348 | h1348
                      · rcases h4bigk with h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h0, hlam, p1349_1]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1192, hlam, p1349_1]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1348, hc04, hc45, hlam, hphi, ht0b, ht5b, p1349_1]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1192, h1346, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1349_1]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1341, hlam, p1349_1]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1341, h1346, h1348, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1341, h1346, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1339, h1346, h1348, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1346, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1346, h1348, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1346, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1339, hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h0, h1339, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1349_1]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1346, hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1339, h829, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1349_1, u2elo2]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1340, hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1345, hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1347, hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [h1348, hlam, p1349_0]
                        · have p1349_0 := h1349c.1
                          have p1349_1 := h1349c.2.1
                          have p1349_2 := h1349c.2.2.1
                          have p1349_3 := h1349c.2.2.2
                          linarith only [hlam, p1349_0]
                      · rcases h4bigk with h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h0, hlam, p1375_1]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1192, hlam, p1375_1]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h0, h1341, h1346, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h0, h1341, h1346, h1348, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1341, h1346, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1341, hlam, p1375_1]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1341, h1346, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1341, h1346, h1348, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1340, h1346, h1348, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1346, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1346, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1346, h1348, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1375_1, u2elo2]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1339, hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h0, h1340, h1348, hlam, p1375_1]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1346, hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1348, hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1340, hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1345, hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1347, hlam, p1375_0]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [h1340, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1]
                        · have p1375_0 := h1375c.1
                          have p1375_1 := h1375c.2.1
                          have p1375_2 := h1375c.2.2.1
                          have p1375_3 := h1375c.2.2.2
                          linarith only [hlam, p1375_0]
                    · linarith only [h0, h1340, h1341, h1347, hlam]
                  · linarith only [h1339, h1346, h829, hlam]
                · linarith only [h0, h1340, h1345, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1404 | h1404
            · linarith only [h1192, h1404, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1406 | h1406
              · linarith only [h0, h1255, h1340, h1404, h1406, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1408 | h1408
                · linarith only [h0, h1340, h1404, h1408, hc01, hlam, hphi, ht12, u2elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1410 | h1410
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1411 | h1411
                    · linarith only [h0, h1408, h1410, h1411, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1413 | h1413
                      · linarith only [h1339, h1340, h1413, hlam]
                      · rcases h4bigk with h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c | h1415c
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h0, hlam, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1192, hlam, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h0, h1406, h1408, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1415_1, u2elo4]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1340, hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1406, h1408, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1415_1, u2elo4]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1404, hlam, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1404, h1411, hc34, hc45, hlam, hphi, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1408, hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h0, h1411, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1411, hc14, hc45, hlam, hphi, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1411, hc34, hc45, hlam, hphi, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1411, hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1339, hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1410, hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1413, hlam, p1415_0]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [h1404, hc12, hc45, hlam, hphi, ht23, ht34, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [hc34, hc45, hlam, hphi, p1415_1]
                        · have p1415_0 := h1415c.1
                          have p1415_1 := h1415c.2.1
                          have p1415_2 := h1415c.2.2.1
                          have p1415_3 := h1415c.2.2.2
                          linarith only [hlam, p1415_0]
                  · linarith only [h1339, h1410, h829, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1442 | h1442
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1443 | h1443
            · linarith only [h1192, h1443, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1445 | h1445
              · linarith only [h1255, h1443, h1445, hc02, hlam, hphi, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1447 | h1447
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1448 | h1448
                  · linarith only [h1339, h1448, h829, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1450 | h1450
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1451 | h1451
                      · rcases h4bigk with h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h0, hlam, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1192, hlam, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1339, hlam, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1192, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1, u2elo3]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h0, hc01, hc14, hlam, hphi, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1443, hlam, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1443, h1448, h829, hc02, hlam, hphi, p1452_1, u2elo3]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1443, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1, u2elo3]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1442, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1, u2elo3]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1452_1, u2elo3]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1448, hlam, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1, u2elo3]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1442, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1445, h1450, hc12, hc34, hlam, hphi, ht23, p1452_1]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          rcases p1452_3 (m.d 0 4) (by simp) with h1472 | h1472
                          · linarith only [h1339, h1472, hlam]
                          · linarith only [h1442, h1472, hlam]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1442, hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1447, hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1450, hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [h1451, hlam, p1452_0]
                        · have p1452_0 := h1452c.1
                          have p1452_1 := h1452c.2.1
                          have p1452_2 := h1452c.2.2.1
                          have p1452_3 := h1452c.2.2.2
                          linarith only [hlam, p1452_0]
                      · linarith only [h0, h1339, h1442, h1443, h1451, h829, hc02, hlam, hphi, u2elo3]
                    · linarith only [h0, h1442, h1443, h1450, hlam]
                · linarith only [h0, h1442, h1447, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1483 | h1483
            · linarith only [h1192, h1483, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
              · linarith only [h0, h1255, h1442, h1483, h1485, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1487 | h1487
                · linarith only [h1339, h1442, h1483, h1487, h829, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1489 | h1489
                  · linarith only [h1339, h1489, h829, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1491 | h1491
                    · linarith only [h0, h1487, h1491, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1493 | h1493
                      · linarith only [h1483, h1491, h1493, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1489, h1493, h829, hc02, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_12_24_L_0_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_24_L_0_H_I_x0 m hb2 hb4 h0
  · exact r1l7_12_24_L_0_H_I_x1 m hb2 hb4 h0

end R2N4
