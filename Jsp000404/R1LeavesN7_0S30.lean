import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h13284 := hg13284
  rcases h1bigk with h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c | h16985c
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h16987 | h16987
    · rcases p16985_3 (m.d 1 2) (by simp) with h16988 | h16988
      · linarith only [h16988, hlam, p16985_0]
      · rcases p16985_3 (m.d 1 3) (by simp) with h16990 | h16990
        · linarith only [h1, h16990, hlam]
        · rcases p16985_3 (m.d 1 4) (by simp) with h16992 | h16992
          · linarith only [h16992, h2, hlam]
          · rcases p16985_3 (m.d 1 5) (by simp) with h16994 | h16994
            · linarith only [h16994, h3, hlam]
            · rcases h1emax with h16996 | h16996 | h16996 | h16996 | h16996
              · linarith only [h16971, h16978, h16982, h16996, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16985_1]
              · rcases h2bigk with h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c | h16998c
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  rcases p16998_3 (m.d 0 2) (by simp) with h17000 | h17000
                  · rcases p16998_3 (m.d 1 2) (by simp) with h17001 | h17001
                    · linarith only [h0, h17001, hlam]
                    · rcases p16998_3 (m.d 2 3) (by simp) with h17003 | h17003
                      · linarith only [h17003, h4, hlam]
                      · rcases p16998_3 (m.d 2 4) (by simp) with h17005 | h17005
                        · linarith only [h17005, h5, hlam]
                        · rcases p16998_3 (m.d 2 5) (by simp) with h17007 | h17007
                          · linarith only [h17007, h6, hlam]
                          · rcases h4bigk with h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c | h17009c
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h14159, h16984, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h7, hlam, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h14159, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h2, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h14159, h16978, h16984, h2, hc23, hc34, hlam, hphi, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16972, hlam, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16976, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h5, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16970, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16978, hlam, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16982, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              rcases p17009_3 (m.d 0 4) (by simp) with h17025 | h17025
                              · linarith only [h17025, h7, hlam]
                              · rcases p17009_3 (m.d 1 4) (by simp) with h17027 | h17027
                                · linarith only [h16972, h17027, hlam]
                                · rcases p17009_3 (m.d 2 4) (by simp) with h17029 | h17029
                                  · linarith only [h16978, h17029, hlam]
                                  · rcases p17009_3 (m.d 3 4) (by simp) with h17031 | h17031
                                    · rcases p17009_3 (m.d 4 5) (by simp) with h17032 | h17032
                                      · linarith only [h16984, h17032, hlam]
                                      · linarith only [h14159, h17032, hlam]
                                    · linarith only [h17031, h7, hlam]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              rcases p17009_3 (m.d 0 4) (by simp) with h17036 | h17036
                              · linarith only [h17036, h7, hlam]
                              · linarith only [h17036, h2, hlam]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              rcases p17009_3 (m.d 0 4) (by simp) with h17039 | h17039
                              · linarith only [h17039, h7, hlam]
                              · linarith only [h17039, h5, hlam]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17009_1]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [h16984, hlam, p17009_0]
                            · have p17009_0 := h17009c.1
                              have p17009_1 := h17009c.2.1
                              have p17009_2 := h17009c.2.2.1
                              have p17009_3 := h17009c.2.2.2
                              linarith only [hlam, p17009_0]
                  · linarith only [h0, h17000, hlam]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  rcases p16998_3 (m.d 0 2) (by simp) with h17050 | h17050
                  · rcases p16998_3 (m.d 1 2) (by simp) with h17051 | h17051
                    · linarith only [h0, h17051, hlam]
                    · linarith only [h16969, h17051, hlam]
                  · linarith only [h17050, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  rcases p16998_3 (m.d 0 2) (by simp) with h17055 | h17055
                  · rcases p16998_3 (m.d 1 2) (by simp) with h17056 | h17056
                    · linarith only [h0, h17056, hlam]
                    · linarith only [h16970, h17056, hlam]
                  · linarith only [h17055, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  rcases p16998_3 (m.d 0 2) (by simp) with h17060 | h17060
                  · rcases p16998_3 (m.d 1 2) (by simp) with h17061 | h17061
                    · linarith only [h0, h17061, hlam]
                    · linarith only [h16971, h17061, hlam]
                  · linarith only [h17060, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h0, hlam, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16996, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16978, h16996, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16978, h16982, h16996, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h4, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16969, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16978, hlam, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16980, hlam, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h5, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16970, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h14159, h16970, h16984, h2, hc23, hc34, hlam, hphi, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16982, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h6, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16971, hlam, p16998_0]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16971, h16996, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [h16971, h16996, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16998_1]
                · have p16998_0 := h16998c.1
                  have p16998_1 := h16998c.2.1
                  have p16998_2 := h16998c.2.2.1
                  have p16998_3 := h16998c.2.2.2
                  linarith only [hlam, p16998_0]
              · rcases h2bigk with h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c | h17085c
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  rcases p17085_3 (m.d 0 2) (by simp) with h17087 | h17087
                  · rcases p17085_3 (m.d 1 2) (by simp) with h17088 | h17088
                    · linarith only [h0, h17088, hlam]
                    · rcases p17085_3 (m.d 2 3) (by simp) with h17090 | h17090
                      · linarith only [h17090, h4, hlam]
                      · rcases p17085_3 (m.d 2 4) (by simp) with h17092 | h17092
                        · linarith only [h17092, h5, hlam]
                        · rcases p17085_3 (m.d 2 5) (by simp) with h17094 | h17094
                          · linarith only [h17094, h6, hlam]
                          · rcases h4bigk with h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c | h17096c
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h14159, h16984, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h7, hlam, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h14159, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h2, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h14159, h16978, h16984, h2, hc23, hc34, hlam, hphi, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16972, hlam, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16976, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h5, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16970, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16978, hlam, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16982, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              rcases p17096_3 (m.d 0 4) (by simp) with h17112 | h17112
                              · linarith only [h17112, h7, hlam]
                              · rcases p17096_3 (m.d 1 4) (by simp) with h17114 | h17114
                                · linarith only [h16972, h17114, hlam]
                                · rcases p17096_3 (m.d 2 4) (by simp) with h17116 | h17116
                                  · linarith only [h16978, h17116, hlam]
                                  · rcases p17096_3 (m.d 3 4) (by simp) with h17118 | h17118
                                    · rcases p17096_3 (m.d 4 5) (by simp) with h17119 | h17119
                                      · linarith only [h16984, h17119, hlam]
                                      · linarith only [h14159, h17119, hlam]
                                    · linarith only [h17118, h7, hlam]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              rcases p17096_3 (m.d 0 4) (by simp) with h17123 | h17123
                              · linarith only [h17123, h7, hlam]
                              · linarith only [h17123, h2, hlam]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              rcases p17096_3 (m.d 0 4) (by simp) with h17126 | h17126
                              · linarith only [h17126, h7, hlam]
                              · linarith only [h17126, h5, hlam]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17096_1]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [h16984, hlam, p17096_0]
                            · have p17096_0 := h17096c.1
                              have p17096_1 := h17096c.2.1
                              have p17096_2 := h17096c.2.2.1
                              have p17096_3 := h17096c.2.2.2
                              linarith only [hlam, p17096_0]
                  · linarith only [h0, h17087, hlam]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  rcases p17085_3 (m.d 0 2) (by simp) with h17137 | h17137
                  · rcases p17085_3 (m.d 1 2) (by simp) with h17138 | h17138
                    · linarith only [h0, h17138, hlam]
                    · linarith only [h16969, h17138, hlam]
                  · linarith only [h17137, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  rcases p17085_3 (m.d 0 2) (by simp) with h17142 | h17142
                  · rcases p17085_3 (m.d 1 2) (by simp) with h17143 | h17143
                    · linarith only [h0, h17143, hlam]
                    · linarith only [h16970, h17143, hlam]
                  · linarith only [h17142, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  rcases p17085_3 (m.d 0 2) (by simp) with h17147 | h17147
                  · rcases p17085_3 (m.d 1 2) (by simp) with h17148 | h17148
                    · linarith only [h0, h17148, hlam]
                    · linarith only [h16971, h17148, hlam]
                  · linarith only [h17147, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h0, hlam, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16978, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h4, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16969, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16978, hlam, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16980, hlam, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h5, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16970, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h14159, h16970, h16984, h2, hc23, hc34, hlam, hphi, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16982, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h6, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16971, hlam, p17085_0]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16985_1, p17085_1]
                · have p17085_0 := h17085c.1
                  have p17085_1 := h17085c.2.1
                  have p17085_2 := h17085c.2.2.1
                  have p17085_3 := h17085c.2.2.2
                  linarith only [hlam, p17085_0]
              · rcases h2bigk with h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c | h17172c
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  rcases p17172_3 (m.d 0 2) (by simp) with h17174 | h17174
                  · rcases p17172_3 (m.d 1 2) (by simp) with h17175 | h17175
                    · linarith only [h0, h17175, hlam]
                    · rcases p17172_3 (m.d 2 3) (by simp) with h17177 | h17177
                      · linarith only [h17177, h4, hlam]
                      · rcases p17172_3 (m.d 2 4) (by simp) with h17179 | h17179
                        · linarith only [h17179, h5, hlam]
                        · rcases p17172_3 (m.d 2 5) (by simp) with h17181 | h17181
                          · linarith only [h17181, h6, hlam]
                          · rcases h4bigk with h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c | h17183c
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h14159, h16984, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h7, hlam, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h14159, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h2, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h14159, h16978, h16984, h2, hc23, hc34, hlam, hphi, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16972, hlam, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16976, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h5, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16970, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16978, hlam, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16982, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              rcases p17183_3 (m.d 0 4) (by simp) with h17199 | h17199
                              · linarith only [h17199, h7, hlam]
                              · rcases p17183_3 (m.d 1 4) (by simp) with h17201 | h17201
                                · linarith only [h16972, h17201, hlam]
                                · rcases p17183_3 (m.d 2 4) (by simp) with h17203 | h17203
                                  · linarith only [h16978, h17203, hlam]
                                  · rcases p17183_3 (m.d 3 4) (by simp) with h17205 | h17205
                                    · rcases p17183_3 (m.d 4 5) (by simp) with h17206 | h17206
                                      · linarith only [h16984, h17206, hlam]
                                      · linarith only [h14159, h17206, hlam]
                                    · linarith only [h17205, h7, hlam]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              rcases p17183_3 (m.d 0 4) (by simp) with h17210 | h17210
                              · linarith only [h17210, h7, hlam]
                              · linarith only [h17210, h2, hlam]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              rcases p17183_3 (m.d 0 4) (by simp) with h17213 | h17213
                              · linarith only [h17213, h7, hlam]
                              · linarith only [h17213, h5, hlam]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17183_1]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [h16984, hlam, p17183_0]
                            · have p17183_0 := h17183c.1
                              have p17183_1 := h17183c.2.1
                              have p17183_2 := h17183c.2.2.1
                              have p17183_3 := h17183c.2.2.2
                              linarith only [hlam, p17183_0]
                  · linarith only [h0, h17174, hlam]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  rcases p17172_3 (m.d 0 2) (by simp) with h17224 | h17224
                  · rcases p17172_3 (m.d 1 2) (by simp) with h17225 | h17225
                    · linarith only [h0, h17225, hlam]
                    · linarith only [h16969, h17225, hlam]
                  · linarith only [h17224, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  rcases p17172_3 (m.d 0 2) (by simp) with h17229 | h17229
                  · rcases p17172_3 (m.d 1 2) (by simp) with h17230 | h17230
                    · linarith only [h0, h17230, hlam]
                    · linarith only [h16970, h17230, hlam]
                  · linarith only [h17229, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  rcases p17172_3 (m.d 0 2) (by simp) with h17234 | h17234
                  · rcases p17172_3 (m.d 1 2) (by simp) with h17235 | h17235
                    · linarith only [h0, h17235, hlam]
                    · linarith only [h16971, h17235, hlam]
                  · linarith only [h17234, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h0, hlam, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16978, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h4, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16969, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16978, hlam, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16980, hlam, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h5, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16970, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h14159, h16970, h16984, h2, hc23, hc34, hlam, hphi, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16982, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h6, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16971, hlam, p17172_0]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16985_1, p17172_1]
                · have p17172_0 := h17172c.1
                  have p17172_1 := h17172c.2.1
                  have p17172_2 := h17172c.2.2.1
                  have p17172_3 := h17172c.2.2.2
                  linarith only [hlam, p17172_0]
              · rcases h2bigk with h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c | h17259c
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  rcases p17259_3 (m.d 0 2) (by simp) with h17261 | h17261
                  · rcases p17259_3 (m.d 1 2) (by simp) with h17262 | h17262
                    · linarith only [h0, h17262, hlam]
                    · rcases p17259_3 (m.d 2 3) (by simp) with h17264 | h17264
                      · linarith only [h17264, h4, hlam]
                      · rcases p17259_3 (m.d 2 4) (by simp) with h17266 | h17266
                        · linarith only [h17266, h5, hlam]
                        · rcases p17259_3 (m.d 2 5) (by simp) with h17268 | h17268
                          · linarith only [h17268, h6, hlam]
                          · rcases h4bigk with h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c | h17270c
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h14159, h16984, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h7, hlam, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h14159, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h2, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h14159, h16978, h16984, h2, hc23, hc34, hlam, hphi, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16972, hlam, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16976, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h5, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16970, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16978, hlam, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16982, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              rcases p17270_3 (m.d 0 4) (by simp) with h17286 | h17286
                              · linarith only [h17286, h7, hlam]
                              · rcases p17270_3 (m.d 1 4) (by simp) with h17288 | h17288
                                · linarith only [h16972, h17288, hlam]
                                · rcases p17270_3 (m.d 2 4) (by simp) with h17290 | h17290
                                  · linarith only [h16978, h17290, hlam]
                                  · rcases p17270_3 (m.d 3 4) (by simp) with h17292 | h17292
                                    · rcases p17270_3 (m.d 4 5) (by simp) with h17293 | h17293
                                      · linarith only [h16984, h17293, hlam]
                                      · linarith only [h14159, h17293, hlam]
                                    · linarith only [h17292, h7, hlam]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              rcases p17270_3 (m.d 0 4) (by simp) with h17297 | h17297
                              · linarith only [h17297, h7, hlam]
                              · linarith only [h17297, h2, hlam]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              rcases p17270_3 (m.d 0 4) (by simp) with h17300 | h17300
                              · linarith only [h17300, h7, hlam]
                              · linarith only [h17300, h5, hlam]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17270_1]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [h16984, hlam, p17270_0]
                            · have p17270_0 := h17270c.1
                              have p17270_1 := h17270c.2.1
                              have p17270_2 := h17270c.2.2.1
                              have p17270_3 := h17270c.2.2.2
                              linarith only [hlam, p17270_0]
                  · linarith only [h0, h17261, hlam]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  rcases p17259_3 (m.d 0 2) (by simp) with h17311 | h17311
                  · rcases p17259_3 (m.d 1 2) (by simp) with h17312 | h17312
                    · linarith only [h0, h17312, hlam]
                    · linarith only [h16969, h17312, hlam]
                  · linarith only [h17311, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  rcases p17259_3 (m.d 0 2) (by simp) with h17316 | h17316
                  · rcases p17259_3 (m.d 1 2) (by simp) with h17317 | h17317
                    · linarith only [h0, h17317, hlam]
                    · linarith only [h16970, h17317, hlam]
                  · linarith only [h17316, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  rcases p17259_3 (m.d 0 2) (by simp) with h17321 | h17321
                  · rcases p17259_3 (m.d 1 2) (by simp) with h17322 | h17322
                    · linarith only [h0, h17322, hlam]
                    · linarith only [h16971, h17322, hlam]
                  · linarith only [h17321, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h0, hlam, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16978, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h4, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16969, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16978, hlam, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16980, hlam, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h5, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16970, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h14159, h16970, h16984, h2, hc23, hc34, hlam, hphi, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16982, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h6, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16971, hlam, p17259_0]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16985_1, p17259_1]
                · have p17259_0 := h17259c.1
                  have p17259_1 := h17259c.2.1
                  have p17259_2 := h17259c.2.2.1
                  have p17259_3 := h17259c.2.2.2
                  linarith only [hlam, p17259_0]
    · linarith only [h16987, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h17347 | h17347
    · rcases p16985_3 (m.d 1 2) (by simp) with h17348 | h17348
      · linarith only [h0, h17348, hlam]
      · linarith only [h16969, h17348, hlam]
    · linarith only [h17347, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h17352 | h17352
    · rcases p16985_3 (m.d 1 2) (by simp) with h17353 | h17353
      · linarith only [h0, h17353, hlam]
      · linarith only [h16970, h17353, hlam]
    · linarith only [h17352, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h17357 | h17357
    · rcases p16985_3 (m.d 1 2) (by simp) with h17358 | h17358
      · linarith only [h0, h17358, hlam]
      · linarith only [h16971, h17358, hlam]
    · linarith only [h17357, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h0, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h17364 | h17364
    · rcases p16985_3 (m.d 1 2) (by simp) with h17365 | h17365
      · rcases p16985_3 (m.d 1 3) (by simp) with h17366 | h17366
        · linarith only [h16969, h17366, hlam]
        · rcases p16985_3 (m.d 1 4) (by simp) with h17368 | h17368
          · linarith only [h16970, h17368, hlam]
          · linarith only [h16972, h17368, hlam]
      · linarith only [h16969, h17365, hlam]
    · linarith only [h1, h17364, hlam]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h17373 | h17373
    · rcases p16985_3 (m.d 1 2) (by simp) with h17374 | h17374
      · rcases p16985_3 (m.d 1 3) (by simp) with h17375 | h17375
        · linarith only [h16969, h17375, hlam]
        · rcases p16985_3 (m.d 1 4) (by simp) with h17377 | h17377
          · linarith only [h16970, h17377, hlam]
          · rcases p16985_3 (m.d 1 5) (by simp) with h17379 | h17379
            · linarith only [h16971, h17379, hlam]
            · linarith only [h16976, h17379, hlam]
      · linarith only [h16970, h17374, hlam]
    · linarith only [h17373, h2, hlam]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    rcases p16985_3 (m.d 0 1) (by simp) with h17384 | h17384
    · rcases p16985_3 (m.d 1 2) (by simp) with h17385 | h17385
      · rcases p16985_3 (m.d 1 3) (by simp) with h17386 | h17386
        · linarith only [h16969, h17386, hlam]
        · rcases p16985_3 (m.d 1 4) (by simp) with h17388 | h17388
          · linarith only [h16970, h17388, hlam]
          · rcases p16985_3 (m.d 1 5) (by simp) with h17390 | h17390
            · linarith only [h16971, h17390, hlam]
            · rcases h1emax with h17392 | h17392 | h17392 | h17392 | h17392
              · linarith only [h0, h16970, h16976, h16978, h17392, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16985_1]
              · linarith only [h16970, h16976, h16978, h17392, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16985_1]
              · rcases h2bigk with h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c | h17395c
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16970, h16976, h16978, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  rcases p17395_3 (m.d 0 2) (by simp) with h17398 | h17398
                  · rcases p17395_3 (m.d 1 2) (by simp) with h17399 | h17399
                    · linarith only [h0, h17399, hlam]
                    · linarith only [h16969, h17399, hlam]
                  · linarith only [h17398, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  rcases p17395_3 (m.d 0 2) (by simp) with h17403 | h17403
                  · rcases p17395_3 (m.d 1 2) (by simp) with h17404 | h17404
                    · linarith only [h0, h17404, hlam]
                    · linarith only [h16970, h17404, hlam]
                  · linarith only [h17403, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  rcases p17395_3 (m.d 0 2) (by simp) with h17408 | h17408
                  · rcases p17395_3 (m.d 1 2) (by simp) with h17409 | h17409
                    · linarith only [h0, h17409, hlam]
                    · linarith only [h16971, h17409, hlam]
                  · linarith only [h17408, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h0, hlam, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  rcases p17395_3 (m.d 0 2) (by simp) with h17415 | h17415
                  · rcases p17395_3 (m.d 1 2) (by simp) with h17416 | h17416
                    · rcases p17395_3 (m.d 2 3) (by simp) with h17417 | h17417
                      · linarith only [h17417, hlam, p17395_0]
                      · rcases p17395_3 (m.d 2 4) (by simp) with h17419 | h17419
                        · linarith only [h16970, h17419, hlam]
                        · linarith only [h16978, h17419, hlam]
                    · linarith only [h17416, hlam, p17395_0]
                  · linarith only [h17415, h4, hlam]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  rcases p17395_3 (m.d 0 2) (by simp) with h17424 | h17424
                  · rcases p17395_3 (m.d 1 2) (by simp) with h17425 | h17425
                    · rcases p17395_3 (m.d 2 3) (by simp) with h17426 | h17426
                      · linarith only [h16969, h17426, hlam]
                      · rcases p17395_3 (m.d 2 4) (by simp) with h17428 | h17428
                        · linarith only [h17428, hlam, p17395_0]
                        · rcases p17395_3 (m.d 2 5) (by simp) with h17430 | h17430
                          · linarith only [h16971, h17430, hlam]
                          · linarith only [h16982, h17430, hlam]
                    · linarith only [h17425, hlam, p17395_0]
                  · linarith only [h17424, h5, hlam]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  rcases p17395_3 (m.d 0 2) (by simp) with h17435 | h17435
                  · rcases p17395_3 (m.d 1 2) (by simp) with h17436 | h17436
                    · rcases p17395_3 (m.d 2 3) (by simp) with h17437 | h17437
                      · linarith only [h16969, h17437, hlam]
                      · rcases p17395_3 (m.d 2 4) (by simp) with h17439 | h17439
                        · linarith only [h16970, h17439, hlam]
                        · rcases p17395_3 (m.d 2 5) (by simp) with h17441 | h17441
                          · linarith only [h17441, hlam, p17395_0]
                          · rcases h4bigk with h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c | h17443c
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h14159, h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h7, hlam, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h14159, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h2, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h0, h16976, h16978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16972, hlam, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16976, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h5, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16970, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16978, hlam, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16982, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              rcases p17443_3 (m.d 0 4) (by simp) with h17459 | h17459
                              · linarith only [h17459, h7, hlam]
                              · rcases p17443_3 (m.d 1 4) (by simp) with h17461 | h17461
                                · linarith only [h16972, h17461, hlam]
                                · rcases p17443_3 (m.d 2 4) (by simp) with h17463 | h17463
                                  · linarith only [h16978, h17463, hlam]
                                  · rcases p17443_3 (m.d 3 4) (by simp) with h17465 | h17465
                                    · rcases p17443_3 (m.d 4 5) (by simp) with h17466 | h17466
                                      · linarith only [h16984, h17466, hlam]
                                      · linarith only [h14159, h17466, hlam]
                                    · linarith only [h17465, h7, hlam]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              rcases p17443_3 (m.d 0 4) (by simp) with h17470 | h17470
                              · linarith only [h17470, h7, hlam]
                              · linarith only [h17470, h2, hlam]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              rcases p17443_3 (m.d 0 4) (by simp) with h17473 | h17473
                              · linarith only [h17473, h7, hlam]
                              · linarith only [h17473, h5, hlam]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17443_1]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [h16984, hlam, p17443_0]
                            · have p17443_0 := h17443c.1
                              have p17443_1 := h17443c.2.1
                              have p17443_2 := h17443c.2.2.1
                              have p17443_3 := h17443c.2.2.2
                              linarith only [hlam, p17443_0]
                    · linarith only [h17436, hlam, p17395_0]
                  · linarith only [h17435, h6, hlam]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h4, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16969, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16978, hlam, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16980, hlam, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h5, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16970, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h0, h16970, h16976, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16982, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h6, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h16971, hlam, p17395_0]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16985_1, p17395_1]
                · have p17395_0 := h17395c.1
                  have p17395_1 := h17395c.2.1
                  have p17395_2 := h17395c.2.2.1
                  have p17395_3 := h17395c.2.2.2
                  linarith only [hlam, p17395_0]
              · rcases h2bigk with h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c | h17500c
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [hc02, hc15, hlam, hphi, ht0b, ht5b, p16985_1, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  rcases p17500_3 (m.d 0 2) (by simp) with h17503 | h17503
                  · rcases p17500_3 (m.d 1 2) (by simp) with h17504 | h17504
                    · linarith only [h0, h17504, hlam]
                    · linarith only [h16969, h17504, hlam]
                  · linarith only [h17503, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  rcases p17500_3 (m.d 0 2) (by simp) with h17508 | h17508
                  · rcases p17500_3 (m.d 1 2) (by simp) with h17509 | h17509
                    · linarith only [h0, h17509, hlam]
                    · linarith only [h16970, h17509, hlam]
                  · linarith only [h17508, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  rcases p17500_3 (m.d 0 2) (by simp) with h17513 | h17513
                  · rcases p17500_3 (m.d 1 2) (by simp) with h17514 | h17514
                    · linarith only [h0, h17514, hlam]
                    · linarith only [h16971, h17514, hlam]
                  · linarith only [h17513, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h0, hlam, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  rcases p17500_3 (m.d 0 2) (by simp) with h17520 | h17520
                  · rcases p17500_3 (m.d 1 2) (by simp) with h17521 | h17521
                    · rcases p17500_3 (m.d 2 3) (by simp) with h17522 | h17522
                      · linarith only [h17522, hlam, p17500_0]
                      · rcases p17500_3 (m.d 2 4) (by simp) with h17524 | h17524
                        · linarith only [h16970, h17524, hlam]
                        · linarith only [h16978, h17524, hlam]
                    · linarith only [h17521, hlam, p17500_0]
                  · linarith only [h17520, h4, hlam]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  rcases p17500_3 (m.d 0 2) (by simp) with h17529 | h17529
                  · rcases p17500_3 (m.d 1 2) (by simp) with h17530 | h17530
                    · rcases p17500_3 (m.d 2 3) (by simp) with h17531 | h17531
                      · linarith only [h16969, h17531, hlam]
                      · rcases p17500_3 (m.d 2 4) (by simp) with h17533 | h17533
                        · linarith only [h17533, hlam, p17500_0]
                        · rcases p17500_3 (m.d 2 5) (by simp) with h17535 | h17535
                          · linarith only [h16971, h17535, hlam]
                          · linarith only [h16982, h17535, hlam]
                    · linarith only [h17530, hlam, p17500_0]
                  · linarith only [h17529, h5, hlam]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  rcases p17500_3 (m.d 0 2) (by simp) with h17540 | h17540
                  · rcases p17500_3 (m.d 1 2) (by simp) with h17541 | h17541
                    · rcases p17500_3 (m.d 2 3) (by simp) with h17542 | h17542
                      · linarith only [h16969, h17542, hlam]
                      · rcases p17500_3 (m.d 2 4) (by simp) with h17544 | h17544
                        · linarith only [h16970, h17544, hlam]
                        · rcases p17500_3 (m.d 2 5) (by simp) with h17546 | h17546
                          · linarith only [h17546, hlam, p17500_0]
                          · rcases h4bigk with h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c | h17548c
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h14159, h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h7, hlam, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h14159, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h2, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16976, h16978, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16985_1, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16972, hlam, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16976, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h5, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16970, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16978, hlam, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16982, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              rcases p17548_3 (m.d 0 4) (by simp) with h17564 | h17564
                              · linarith only [h17564, h7, hlam]
                              · rcases p17548_3 (m.d 1 4) (by simp) with h17566 | h17566
                                · linarith only [h16972, h17566, hlam]
                                · rcases p17548_3 (m.d 2 4) (by simp) with h17568 | h17568
                                  · linarith only [h16978, h17568, hlam]
                                  · rcases p17548_3 (m.d 3 4) (by simp) with h17570 | h17570
                                    · rcases p17548_3 (m.d 4 5) (by simp) with h17571 | h17571
                                      · linarith only [h16984, h17571, hlam]
                                      · linarith only [h14159, h17571, hlam]
                                    · linarith only [h17570, h7, hlam]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              rcases p17548_3 (m.d 0 4) (by simp) with h17575 | h17575
                              · linarith only [h17575, h7, hlam]
                              · linarith only [h17575, h2, hlam]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              rcases p17548_3 (m.d 0 4) (by simp) with h17578 | h17578
                              · linarith only [h17578, h7, hlam]
                              · linarith only [h17578, h5, hlam]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17548_1]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [h16984, hlam, p17548_0]
                            · have p17548_0 := h17548c.1
                              have p17548_1 := h17548c.2.1
                              have p17548_2 := h17548c.2.2.1
                              have p17548_3 := h17548c.2.2.2
                              linarith only [hlam, p17548_0]
                    · linarith only [h17541, hlam, p17500_0]
                  · linarith only [h17540, h6, hlam]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h4, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h16969, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h16978, hlam, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h16980, hlam, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h5, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h16970, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h0, h16971, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h16982, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h6, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h16971, hlam, p17500_0]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16985_1, p17500_1]
                · have p17500_0 := h17500c.1
                  have p17500_1 := h17500c.2.1
                  have p17500_2 := h17500c.2.2.1
                  have p17500_3 := h17500c.2.2.2
                  linarith only [hlam, p17500_0]
              · rcases h2bigk with h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c | h17605c
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [hc02, hc15, hlam, hphi, ht0b, ht5b, p16985_1, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  rcases p17605_3 (m.d 0 2) (by simp) with h17608 | h17608
                  · rcases p17605_3 (m.d 1 2) (by simp) with h17609 | h17609
                    · linarith only [h0, h17609, hlam]
                    · linarith only [h16969, h17609, hlam]
                  · linarith only [h17608, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  rcases p17605_3 (m.d 0 2) (by simp) with h17613 | h17613
                  · rcases p17605_3 (m.d 1 2) (by simp) with h17614 | h17614
                    · linarith only [h0, h17614, hlam]
                    · linarith only [h16970, h17614, hlam]
                  · linarith only [h17613, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  rcases p17605_3 (m.d 0 2) (by simp) with h17618 | h17618
                  · rcases p17605_3 (m.d 1 2) (by simp) with h17619 | h17619
                    · linarith only [h0, h17619, hlam]
                    · linarith only [h16971, h17619, hlam]
                  · linarith only [h17618, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h0, hlam, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  rcases p17605_3 (m.d 0 2) (by simp) with h17625 | h17625
                  · rcases p17605_3 (m.d 1 2) (by simp) with h17626 | h17626
                    · rcases p17605_3 (m.d 2 3) (by simp) with h17627 | h17627
                      · linarith only [h17627, hlam, p17605_0]
                      · rcases p17605_3 (m.d 2 4) (by simp) with h17629 | h17629
                        · linarith only [h16970, h17629, hlam]
                        · linarith only [h16978, h17629, hlam]
                    · linarith only [h17626, hlam, p17605_0]
                  · linarith only [h17625, h4, hlam]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  rcases p17605_3 (m.d 0 2) (by simp) with h17634 | h17634
                  · rcases p17605_3 (m.d 1 2) (by simp) with h17635 | h17635
                    · rcases p17605_3 (m.d 2 3) (by simp) with h17636 | h17636
                      · linarith only [h16969, h17636, hlam]
                      · rcases p17605_3 (m.d 2 4) (by simp) with h17638 | h17638
                        · linarith only [h17638, hlam, p17605_0]
                        · rcases p17605_3 (m.d 2 5) (by simp) with h17640 | h17640
                          · linarith only [h16971, h17640, hlam]
                          · linarith only [h16982, h17640, hlam]
                    · linarith only [h17635, hlam, p17605_0]
                  · linarith only [h17634, h5, hlam]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  rcases p17605_3 (m.d 0 2) (by simp) with h17645 | h17645
                  · rcases p17605_3 (m.d 1 2) (by simp) with h17646 | h17646
                    · rcases p17605_3 (m.d 2 3) (by simp) with h17647 | h17647
                      · linarith only [h16969, h17647, hlam]
                      · rcases p17605_3 (m.d 2 4) (by simp) with h17649 | h17649
                        · linarith only [h16970, h17649, hlam]
                        · rcases p17605_3 (m.d 2 5) (by simp) with h17651 | h17651
                          · linarith only [h17651, hlam, p17605_0]
                          · rcases h4bigk with h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c | h17653c
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h14159, h16969, h16972, h16984, hc23, hc34, hlam, hphi, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h14159, h16978, h16984, hc23, hc34, hlam, hphi, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h7, hlam, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h14159, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h2, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16976, h16978, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16985_1, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16972, hlam, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16976, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h5, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16970, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16978, hlam, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16982, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              rcases p17653_3 (m.d 0 4) (by simp) with h17669 | h17669
                              · linarith only [h17669, h7, hlam]
                              · rcases p17653_3 (m.d 1 4) (by simp) with h17671 | h17671
                                · linarith only [h16972, h17671, hlam]
                                · rcases p17653_3 (m.d 2 4) (by simp) with h17673 | h17673
                                  · linarith only [h16978, h17673, hlam]
                                  · rcases p17653_3 (m.d 3 4) (by simp) with h17675 | h17675
                                    · rcases p17653_3 (m.d 4 5) (by simp) with h17676 | h17676
                                      · linarith only [h16984, h17676, hlam]
                                      · linarith only [h14159, h17676, hlam]
                                    · linarith only [h17675, h7, hlam]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              rcases p17653_3 (m.d 0 4) (by simp) with h17680 | h17680
                              · linarith only [h17680, h7, hlam]
                              · linarith only [h17680, h2, hlam]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              rcases p17653_3 (m.d 0 4) (by simp) with h17683 | h17683
                              · linarith only [h17683, h7, hlam]
                              · linarith only [h17683, h5, hlam]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h14159, h16978, h5, hc23, hc34, hlam, hphi, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h1, h16969, h16984, h7, hc23, hc34, hlam, hphi, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16970, h16978, h16984, hc23, hc34, hlam, hphi, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16978, h16984, hc23, hc34, hlam, hphi, p17653_1]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [h16984, hlam, p17653_0]
                            · have p17653_0 := h17653c.1
                              have p17653_1 := h17653c.2.1
                              have p17653_2 := h17653c.2.2.1
                              have p17653_3 := h17653c.2.2.2
                              linarith only [hlam, p17653_0]
                    · linarith only [h17646, hlam, p17605_0]
                  · linarith only [h17645, h6, hlam]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h4, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h16969, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h16978, hlam, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h16980, hlam, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h5, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h16970, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h0, h16971, h16982, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h16982, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h6, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h16971, hlam, p17605_0]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16985_1, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p16985_1, p17605_1]
                · have p17605_0 := h17605c.1
                  have p17605_1 := h17605c.2.1
                  have p17605_2 := h17605c.2.2.1
                  have p17605_3 := h17605c.2.2.2
                  linarith only [hlam, p17605_0]
      · linarith only [h16971, h17385, hlam]
    · linarith only [h17384, h3, hlam]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h1, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h16969, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h16972, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h16974, hlam, p16985_1]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h2, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h16970, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h14159, h16969, h16984, h2, hc23, hc34, hlam, hphi, p16985_1]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h16976, hlam, p16985_1]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h3, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h16971, hlam, p16985_0]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h14159, h16969, h16984, h3, hc23, hc34, hlam, hphi, p16985_1]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [h14159, h16969, h16972, h16984, h3, hc23, hc34, hlam, hphi, p16985_1]
  · have p16985_0 := h16985c.1
    have p16985_1 := h16985c.2.1
    have p16985_2 := h16985c.2.2.1
    have p16985_3 := h16985c.2.2.2
    linarith only [hlam, p16985_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [hlam, p17727_0]

end R2N4
