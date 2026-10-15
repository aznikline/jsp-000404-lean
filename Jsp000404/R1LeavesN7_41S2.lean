import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h833 | h833
  · rcases m.htr 1 3 5 (by decide) (by decide) with h834 | h834
    · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
      · linarith only [h0, h2, h835, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
        · rcases m.htr 2 3 5 (by decide) (by decide) with h838 | h838
          · rcases m.htr 2 4 5 (by decide) (by decide) with h839 | h839
            · linarith only [h1, h2, h839, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h841 | h841
              · linarith only [h837, h839, h841, hlam]
              · rcases h5bigk with h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h833, hc25, hlam, hphi, ht01, ht0b, ht5b, p843_1, u1elo0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p843_1, u1elo0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h841, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p843_1, u1elo0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h2, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h839, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p843_1, u1elo0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h841, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p843_1, u1elo0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h835, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h1, hlam, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h833, hlam, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h1, h841, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h839, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h834, hc05, hlam, hphi, ht01, ht0b, ht5b, p843_1, u1elo2]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h834, hlam, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h838, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h841, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h835, hc14, hc45, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h835, hc14, hc45, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h837, h839, hc34, hc45, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h841, hc34, hc45, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
          · linarith only [h834, h837, h838, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h870 | h870
          · rcases m.htr 2 4 5 (by decide) (by decide) with h871 | h871
            · linarith only [h0, h2, h833, h871, hlam]
            · linarith only [h837, h870, h871, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h874 | h874
            · linarith only [h1, h2, h874, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h876 | h876
              · linarith only [h0, h2, h834, h876, hlam]
              · rcases h5bigk with h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h834, h837, h876, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h0, h874, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p878_1, u1elo0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h2, h876, hc34, hc45, hlam, hphi, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h2, hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h0, hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h0, h837, h874, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p878_1, u1elo0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h0, h876, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p878_1, u1elo0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h835, hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h1, hlam, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h833, hlam, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h870, hlam, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h874, hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h1, h837, h874, hc23, hc35, hlam, hphi, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h834, hlam, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h834, h837, h874, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p878_1, u1elo4]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h876, hlam, p878_0]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h1, h837, h874, hc23, hc45, hlam, hphi, ht34, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h833, h837, h874, hc23, hc45, hlam, hphi, ht34, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h837, h874, hc23, hc45, hlam, hphi, ht34, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [h870, hc23, hc45, hlam, hphi, ht34, p878_1]
                · have p878_0 := h878c.1
                  have p878_1 := h878c.2.1
                  have p878_2 := h878c.2.2.1
                  have p878_3 := h878c.2.2.2
                  linarith only [hlam, p878_0]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h904 | h904
      · linarith only [h0, h2, h904, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h906 | h906
        · rcases m.htr 2 3 5 (by decide) (by decide) with h907 | h907
          · linarith only [h833, h834, h907, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h909 | h909
            · linarith only [h0, h2, h833, h906, h907, h909, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h911 | h911
              · linarith only [h0, h2, h833, h906, h907, h911, hlam]
              · rcases h5bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p913_1, u1elo0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p913_1, u1elo0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h906, h907, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h2, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h906, h907, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p913_1, u1elo4]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h834, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h904, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h1, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h833, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h907, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h909, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h1, h906, h907, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h833, h906, h907, h911, hc34, hc45, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h906, h907, h911, hc34, hc45, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h911, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, h833, h906, h907, hc34, hc45, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h833, h906, h907, hc34, hc45, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h906, h907, hc34, hc45, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h834, hc13, hc45, hlam, hphi, ht34, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h939 | h939
          · linarith only [h834, h906, h939, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h941 | h941
            · linarith only [h0, h2, h833, h941, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h943 | h943
              · rcases h5bigk with h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p944_1, u1elo0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p944_1, u1elo0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h2, h943, hlam, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h2, hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h0, hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h906, h941, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p944_1, u1elo4]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h834, hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h904, hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h1, hlam, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h833, hlam, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h939, hlam, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h941, hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h1, h906, h941, hc23, hc35, hlam, hphi, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h833, h906, h941, hc23, hc35, hlam, hphi, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h906, h941, hc23, hc35, hlam, hphi, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [hlam, p944_0]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h2, h943, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h0, h833, h906, h941, hc23, hc45, hlam, hphi, ht34, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h833, h906, h941, hc23, hc45, hlam, hphi, ht34, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h906, h941, hc23, hc45, hlam, hphi, ht34, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [h943, hlam, p944_1]
                · have p944_0 := h944c.1
                  have p944_1 := h944c.2.1
                  have p944_2 := h944c.2.2.1
                  have p944_3 := h944c.2.2.2
                  linarith only [hlam, p944_0]
              · rcases h5bigk with h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h0, h833, h906, h941, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p970_1, u1elo0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h0, h906, h941, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p970_1, u1elo0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p970_1, u1elo0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h2, hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h0, hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h906, h941, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p970_1, u1elo4]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h834, hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h904, hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h1, hlam, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h833, hlam, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h939, hlam, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h941, hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h1, h906, h941, hc23, hc35, hlam, hphi, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h833, h906, h941, hc23, hc35, hlam, hphi, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h906, h941, hc23, hc35, hlam, hphi, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h943, hlam, p970_0]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h0, h833, h906, h941, hc23, hc45, hlam, hphi, ht34, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h833, h906, h941, hc23, hc45, hlam, hphi, ht34, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h906, h941, hc23, hc45, hlam, hphi, ht34, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [h834, hc13, hc45, hlam, hphi, ht34, p970_1]
                · have p970_0 := h970c.1
                  have p970_1 := h970c.2.1
                  have p970_2 := h970c.2.2.1
                  have p970_3 := h970c.2.2.2
                  linarith only [hlam, p970_0]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h996 | h996
    · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
      · linarith only [h0, h2, h997, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h999 | h999
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1000 | h1000
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1001 | h1001
            · linarith only [h1, h1001, h2, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1003 | h1003
              · linarith only [h1, h1003, h2, h833, h999, hc12, hc23, hlam, hphi]
              · rcases h5bigk with h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p1005_1, u1elo0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h833, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h0, h1003, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1005_1, u1elo0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h2, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h0, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h833, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1003, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1005_1, u1elo4]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h997, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1, hlam, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h0, h1, h1003, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1005_1, u1elo0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1001, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h996, hc05, hlam, hphi, ht01, ht0b, ht5b, p1005_1, u1elo2]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h996, hlam, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1000, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1003, hlam, p1005_0]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h0, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [h1003, hc34, hc45, hlam, hphi, p1005_1]
                · have p1005_0 := h1005c.1
                  have p1005_1 := h1005c.2.1
                  have p1005_2 := h1005c.2.2.1
                  have p1005_3 := h1005c.2.2.2
                  linarith only [hlam, p1005_0]
          · linarith only [h0, h1000, h996, h999, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1032 | h1032
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1033 | h1033
            · linarith only [h1, h1033, h2, hlam]
            · linarith only [h1032, h1033, h999, hlam]
          · linarith only [h1032, h833, h996, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
      · linarith only [h1, h1037, h2, h833, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1040 | h1040
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1041 | h1041
            · linarith only [h1, h1041, h2, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1043 | h1043
              · linarith only [h1039, h1041, h1043, hlam]
              · rcases h5bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p1045_1, u1elo0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h833, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1045_1, u1elo0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h2, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h0, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h833, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h996, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1037, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1, hlam, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h833, hc12, hc25, hlam, hphi, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h0, h1, h996, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1045_1, u1elo0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1041, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h0, h833, hc12, hc35, hlam, hphi, ht23, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h833, hc12, hc35, hlam, hphi, ht23, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1040, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1043, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h996, hc13, hc45, hlam, hphi, ht34, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1071 | h1071
            · linarith only [h1, h1039, h1040, h1071, h2, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1073 | h1073
              · linarith only [h1, h1039, h1040, h1073, h2, hlam]
              · rcases h5bigk with h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h2, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p1075_1, u1elo0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h0, h1040, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1075_1, u1elo0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h2, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h0, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h833, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h996, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h1037, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h1, hlam, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h833, hc12, hc25, hlam, hphi, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h1040, hlam, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h1071, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h0, h833, hc12, hc35, hlam, hphi, ht23, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h833, hc12, hc35, hlam, hphi, ht23, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h833, hc12, hc35, hlam, hphi, ht23, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h1073, hlam, p1075_0]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h1, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [h996, hc13, hc45, hlam, hphi, ht34, p1075_1]
                · have p1075_0 := h1075c.1
                  have p1075_1 := h1075c.2.1
                  have p1075_2 := h1075c.2.2.1
                  have p1075_3 := h1075c.2.2.2
                  linarith only [hlam, p1075_0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1101 | h1101
          · linarith only [h1039, h1101, h996, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1103 | h1103
            · linarith only [h1, h1103, h2, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1105 | h1105
              · rcases h5bigk with h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1105, h2, h833, hc12, hc35, hlam, hphi, ht23, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h0, h833, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1106_1, u1elo0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1105, h2, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h2, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h0, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h833, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h996, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1037, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, hlam, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h833, hc12, hc25, hlam, hphi, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1101, hlam, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1103, hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h0, h833, hc12, hc35, hlam, hphi, ht23, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1105, h833, hc12, hc34, hlam, hphi, ht23, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1105, h833, hc12, hc34, hlam, hphi, ht23, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1039, h1103, h1105, hc23, hc34, hlam, hphi, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [h1105, hlam, p1106_1]
                · have p1106_0 := h1106c.1
                  have p1106_1 := h1106c.2.1
                  have p1106_2 := h1106c.2.2.1
                  have p1106_3 := h1106c.2.2.2
                  linarith only [hlam, p1106_0]
              · rcases h5bigk with h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h0, h833, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u1elo0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h0, h833, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u1elo0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1132_1, u1elo0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h2, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h0, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h833, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h996, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h1037, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h1, hlam, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h833, hc12, hc25, hlam, hphi, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h1101, hlam, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h1103, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h0, h833, hc12, hc35, hlam, hphi, ht23, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h833, hc12, hc35, hlam, hphi, ht23, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h833, hc12, hc35, hlam, hphi, ht23, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h1105, hlam, p1132_0]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h1, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h833, hc12, hc45, hlam, hphi, ht23, ht34, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [h996, hc13, hc45, hlam, hphi, ht34, p1132_1]
                · have p1132_0 := h1132c.1
                  have p1132_1 := h1132c.2.1
                  have p1132_2 := h1132c.2.2.1
                  have p1132_3 := h1132c.2.2.2
                  linarith only [hlam, p1132_0]

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x0 m hb1 hb2 hb5 h0 h1 h2
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x1 m hb1 hb2 hb5 h0 h1 h2

end R2N4
