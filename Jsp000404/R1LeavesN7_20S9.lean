import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5037 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5897 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 1 2 3 (by decide) (by decide) with h5898 | h5898
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5899 | h5899
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5900 | h5900
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5901 | h5901
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5902 | h5902
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5903 | h5903
            · linarith only [h5034, h5037, h5903, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5905 | h5905
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5906 | h5906
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5907 | h5907
                  · rcases h2bigk with h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h0, hlam, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5905, h5907, hc02, hc45, hlam, hphi, ht0b, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h0, h5903, h5905, h5907, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      rcases p5908_3 (m.d 0 2) (by simp) with h5913 | h5913
                      · rcases p5908_3 (m.d 1 2) (by simp) with h5914 | h5914
                        · rcases p5908_3 (m.d 2 3) (by simp) with h5915 | h5915
                          · linarith only [h5034, h5915, hlam]
                          · linarith only [h5905, h5915, hlam]
                        · linarith only [h5900, h5914, hlam]
                      · linarith only [h5913, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5905, h5907, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5903, h5905, h5907, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      rcases p5908_3 (m.d 0 2) (by simp) with h5924 | h5924
                      · linarith only [h0, h5924, hlam]
                      · linarith only [h5036, h5924, hlam]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5034, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5898, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5903, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5035, h5903, h5905, h5907, hc02, hc45, hlam, hphi, ht0b, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5035, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5899, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h0, h5035, h5905, h5907, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5036, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5900, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5905, hlam, p5908_1]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [h5906, hlam, p5908_0]
                    · have p5908_0 := h5908c.1
                      have p5908_1 := h5908c.2.1
                      have p5908_2 := h5908c.2.2.1
                      have p5908_3 := h5908c.2.2.2
                      linarith only [hlam, p5908_0]
                  · linarith only [h5037, h5897, h5907, hlam]
                · linarith only [h5037, h5897, h5898, h5901, h5903, h5905, h5906, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5944 | h5944
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5945 | h5945
                  · rcases h2bigk with h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c | h5946c
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h0, hlam, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      rcases p5946_3 (m.d 0 2) (by simp) with h5949 | h5949
                      · rcases p5946_3 (m.d 1 2) (by simp) with h5950 | h5950
                        · rcases p5946_3 (m.d 2 3) (by simp) with h5951 | h5951
                          · linarith only [h5951, hlam, p5946_0]
                          · rcases p5946_3 (m.d 2 4) (by simp) with h5953 | h5953
                            · linarith only [h5035, h5953, hlam]
                            · linarith only [h5903, h5953, hlam]
                        · linarith only [h5898, h5950, hlam]
                      · linarith only [h5949, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h0, h5944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      rcases p5946_3 (m.d 0 2) (by simp) with h5959 | h5959
                      · rcases p5946_3 (m.d 1 2) (by simp) with h5960 | h5960
                        · rcases p5946_3 (m.d 2 3) (by simp) with h5961 | h5961
                          · linarith only [h5034, h5961, hlam]
                          · rcases p5946_3 (m.d 2 4) (by simp) with h5963 | h5963
                            · linarith only [h5035, h5963, hlam]
                            · linarith only [h5944, h5963, hlam]
                        · linarith only [h5900, h5960, hlam]
                      · linarith only [h5959, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      rcases p5946_3 (m.d 0 2) (by simp) with h5970 | h5970
                      · linarith only [h0, h5970, hlam]
                      · linarith only [h5034, h5970, hlam]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      rcases p5946_3 (m.d 0 2) (by simp) with h5974 | h5974
                      · linarith only [h0, h5974, hlam]
                      · linarith only [h5036, h5974, hlam]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5034, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5898, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5903, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5905, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5035, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5899, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5035, h5037, h5898, h5901, h5905, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5036, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5900, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5946_1]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [h5944, hlam, p5946_0]
                    · have p5946_0 := h5946c.1
                      have p5946_1 := h5946c.2.1
                      have p5946_2 := h5946c.2.2.1
                      have p5946_3 := h5946c.2.2.2
                      linarith only [hlam, p5946_0]
                  · linarith only [h5037, h5897, h5945, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5993 | h5993
                  · rcases h2bigk with h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c | h5994c
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h0, hlam, p5994_1]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      rcases p5994_3 (m.d 0 2) (by simp) with h5997 | h5997
                      · rcases p5994_3 (m.d 1 2) (by simp) with h5998 | h5998
                        · rcases p5994_3 (m.d 2 3) (by simp) with h5999 | h5999
                          · linarith only [h5999, hlam, p5994_0]
                          · rcases p5994_3 (m.d 2 4) (by simp) with h6001 | h6001
                            · linarith only [h5035, h6001, hlam]
                            · linarith only [h5903, h6001, hlam]
                        · linarith only [h5898, h5998, hlam]
                      · linarith only [h5997, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      rcases p5994_3 (m.d 0 2) (by simp) with h6006 | h6006
                      · rcases p5994_3 (m.d 1 2) (by simp) with h6007 | h6007
                        · rcases p5994_3 (m.d 2 3) (by simp) with h6008 | h6008
                          · linarith only [h5034, h6008, hlam]
                          · rcases p5994_3 (m.d 2 4) (by simp) with h6010 | h6010
                            · linarith only [h6010, hlam, p5994_0]
                            · rcases p5994_3 (m.d 2 5) (by simp) with h6012 | h6012
                              · linarith only [h5036, h6012, hlam]
                              · linarith only [h5944, h6012, hlam]
                        · linarith only [h5899, h6007, hlam]
                      · linarith only [h6006, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      rcases p5994_3 (m.d 0 2) (by simp) with h6017 | h6017
                      · rcases p5994_3 (m.d 1 2) (by simp) with h6018 | h6018
                        · rcases p5994_3 (m.d 2 3) (by simp) with h6019 | h6019
                          · linarith only [h5034, h6019, hlam]
                          · rcases p5994_3 (m.d 2 4) (by simp) with h6021 | h6021
                            · linarith only [h5035, h6021, hlam]
                            · rcases p5994_3 (m.d 2 5) (by simp) with h6023 | h6023
                              · linarith only [h6023, hlam, p5994_0]
                              · rcases h4bigk with h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c | h6025c
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h3667, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  rcases p6025_3 (m.d 0 4) (by simp) with h6028 | h6028
                                  · rcases p6025_3 (m.d 1 4) (by simp) with h6029 | h6029
                                    · rcases p6025_3 (m.d 2 4) (by simp) with h6030 | h6030
                                      · linarith only [h5035, h6030, hlam]
                                      · rcases p6025_3 (m.d 3 4) (by simp) with h6032 | h6032
                                        · rcases p6025_3 (m.d 4 5) (by simp) with h6033 | h6033
                                          · linarith only [h5897, h6033, hlam]
                                          · linarith only [h5944, h6033, hlam]
                                        · linarith only [h5903, h6032, hlam]
                                    · linarith only [h5899, h6029, hlam]
                                  · linarith only [h5035, h6028, hlam]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5037, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5037, h5898, h5901, h5903, h5944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5897, h5903, h5944, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  rcases p6025_3 (m.d 0 4) (by simp) with h6043 | h6043
                                  · linarith only [h3667, h6043, hlam]
                                  · linarith only [h5035, h6043, hlam]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5037, h5897, h5903, h5944, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  rcases p6025_3 (m.d 0 4) (by simp) with h6047 | h6047
                                  · linarith only [h3667, h6047, hlam]
                                  · linarith only [h5897, h6047, hlam]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5035, hlam, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5899, hlam, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5903, hlam, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5944, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5897, h5903, h5944, hc23, hc34, hlam, hphi, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5901, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  rcases p6025_3 (m.d 0 4) (by simp) with h6057 | h6057
                                  · linarith only [h5037, h6057, hlam]
                                  · linarith only [h5035, h6057, hlam]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5898, h5901, h5903, h5944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5897, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5902, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5037, h5897, h5898, h5901, h5903, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6025_1]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [h5993, hlam, p6025_0]
                                · have p6025_0 := h6025c.1
                                  have p6025_1 := h6025c.2.1
                                  have p6025_2 := h6025c.2.2.1
                                  have p6025_3 := h6025c.2.2.2
                                  linarith only [hlam, p6025_0]
                        · linarith only [h5900, h6018, hlam]
                      · linarith only [h6017, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5994_1]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      rcases p5994_3 (m.d 0 2) (by simp) with h6071 | h6071
                      · linarith only [h0, h6071, hlam]
                      · linarith only [h5034, h6071, hlam]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      rcases p5994_3 (m.d 0 2) (by simp) with h6074 | h6074
                      · linarith only [h0, h6074, hlam]
                      · linarith only [h5035, h6074, hlam]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      rcases p5994_3 (m.d 0 2) (by simp) with h6077 | h6077
                      · linarith only [h0, h6077, hlam]
                      · linarith only [h5036, h6077, hlam]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5034, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5898, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5903, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5905, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5035, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5899, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5994_1]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5944, hlam, p5994_1]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5036, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5900, hlam, p5994_0]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5036, h5037, h5897, h5898, h5901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5994_1]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [h5036, h5037, h5897, h5898, h5901, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5994_1]
                    · have p5994_0 := h5994c.1
                      have p5994_1 := h5994c.2.1
                      have p5994_2 := h5994c.2.2.1
                      have p5994_3 := h5994c.2.2.2
                      linarith only [hlam, p5994_0]
                  · linarith only [h5037, h5897, h5993, hlam]
          · linarith only [h3667, h5037, h5897, h5898, h5901, h5902, hc01, hc12, hlam, hphi]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6097 | h6097
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6098 | h6098
            · linarith only [h0, h3667, h5034, h5901, h6098, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6100 | h6100
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6101 | h6101
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6102 | h6102
                  · rcases h2bigk with h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c | h6103c
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h0, hlam, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h0, h6100, h6102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h0, h6098, h6100, h6102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      rcases p6103_3 (m.d 0 2) (by simp) with h6108 | h6108
                      · rcases p6103_3 (m.d 1 2) (by simp) with h6109 | h6109
                        · rcases p6103_3 (m.d 2 3) (by simp) with h6110 | h6110
                          · linarith only [h5034, h6110, hlam]
                          · linarith only [h6100, h6110, hlam]
                        · linarith only [h5900, h6109, hlam]
                      · linarith only [h6108, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h6100, h6102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h6098, h6100, h6102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      rcases p6103_3 (m.d 0 2) (by simp) with h6119 | h6119
                      · linarith only [h0, h6119, hlam]
                      · linarith only [h5036, h6119, hlam]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5034, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5898, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h6098, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5035, h6098, hc02, hc25, hlam, hphi, ht0b, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5035, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5899, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h0, h5035, h6100, h6102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5036, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h5900, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h6100, hlam, p6103_1]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [h6101, hlam, p6103_0]
                    · have p6103_0 := h6103c.1
                      have p6103_1 := h6103c.2.1
                      have p6103_2 := h6103c.2.2.1
                      have p6103_3 := h6103c.2.2.2
                      linarith only [hlam, p6103_0]
                  · linarith only [h3667, h5897, h5901, h6102, hlam]
                · linarith only [h6098, h6100, h6101, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6139 | h6139
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6140 | h6140
                  · rcases h2bigk with h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c | h6141c
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h0, hlam, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      rcases p6141_3 (m.d 0 2) (by simp) with h6144 | h6144
                      · rcases p6141_3 (m.d 1 2) (by simp) with h6145 | h6145
                        · rcases p6141_3 (m.d 2 3) (by simp) with h6146 | h6146
                          · linarith only [h6146, hlam, p6141_0]
                          · rcases p6141_3 (m.d 2 4) (by simp) with h6148 | h6148
                            · linarith only [h5035, h6148, hlam]
                            · linarith only [h6098, h6148, hlam]
                        · linarith only [h5898, h6145, hlam]
                      · linarith only [h6144, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h0, h6139, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      rcases p6141_3 (m.d 0 2) (by simp) with h6154 | h6154
                      · rcases p6141_3 (m.d 1 2) (by simp) with h6155 | h6155
                        · rcases p6141_3 (m.d 2 3) (by simp) with h6156 | h6156
                          · linarith only [h5034, h6156, hlam]
                          · rcases p6141_3 (m.d 2 4) (by simp) with h6158 | h6158
                            · linarith only [h5035, h6158, hlam]
                            · linarith only [h6139, h6158, hlam]
                        · linarith only [h5900, h6155, hlam]
                      · linarith only [h6154, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      rcases p6141_3 (m.d 0 2) (by simp) with h6165 | h6165
                      · linarith only [h0, h6165, hlam]
                      · linarith only [h5034, h6165, hlam]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h6139, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      rcases p6141_3 (m.d 0 2) (by simp) with h6169 | h6169
                      · linarith only [h0, h6169, hlam]
                      · linarith only [h5036, h6169, hlam]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5034, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5898, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h6098, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h6100, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5035, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5899, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h0, h5035, h6100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5036, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h5900, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6141_1]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [h6139, hlam, p6141_0]
                    · have p6141_0 := h6141c.1
                      have p6141_1 := h6141c.2.1
                      have p6141_2 := h6141c.2.2.1
                      have p6141_3 := h6141c.2.2.2
                      linarith only [hlam, p6141_0]
                  · linarith only [h0, h3667, h5035, h5901, h6139, h6140, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6188 | h6188
                  · rcases h2bigk with h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c | h6189c
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h0, hlam, p6189_1]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      rcases p6189_3 (m.d 0 2) (by simp) with h6192 | h6192
                      · rcases p6189_3 (m.d 1 2) (by simp) with h6193 | h6193
                        · rcases p6189_3 (m.d 2 3) (by simp) with h6194 | h6194
                          · linarith only [h6194, hlam, p6189_0]
                          · rcases p6189_3 (m.d 2 4) (by simp) with h6196 | h6196
                            · linarith only [h5035, h6196, hlam]
                            · linarith only [h6098, h6196, hlam]
                        · linarith only [h5898, h6193, hlam]
                      · linarith only [h6192, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      rcases p6189_3 (m.d 0 2) (by simp) with h6201 | h6201
                      · rcases p6189_3 (m.d 1 2) (by simp) with h6202 | h6202
                        · rcases p6189_3 (m.d 2 3) (by simp) with h6203 | h6203
                          · linarith only [h5034, h6203, hlam]
                          · rcases p6189_3 (m.d 2 4) (by simp) with h6205 | h6205
                            · linarith only [h6205, hlam, p6189_0]
                            · rcases p6189_3 (m.d 2 5) (by simp) with h6207 | h6207
                              · linarith only [h5036, h6207, hlam]
                              · linarith only [h6139, h6207, hlam]
                        · linarith only [h5899, h6202, hlam]
                      · linarith only [h6201, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      rcases p6189_3 (m.d 0 2) (by simp) with h6212 | h6212
                      · rcases p6189_3 (m.d 1 2) (by simp) with h6213 | h6213
                        · rcases p6189_3 (m.d 2 3) (by simp) with h6214 | h6214
                          · linarith only [h5034, h6214, hlam]
                          · rcases p6189_3 (m.d 2 4) (by simp) with h6216 | h6216
                            · linarith only [h5035, h6216, hlam]
                            · rcases p6189_3 (m.d 2 5) (by simp) with h6218 | h6218
                              · linarith only [h6218, hlam, p6189_0]
                              · rcases h4bigk with h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c | h6220c
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h3667, hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  rcases p6220_3 (m.d 0 4) (by simp) with h6223 | h6223
                                  · rcases p6220_3 (m.d 1 4) (by simp) with h6224 | h6224
                                    · rcases p6220_3 (m.d 2 4) (by simp) with h6225 | h6225
                                      · linarith only [h5035, h6225, hlam]
                                      · rcases p6220_3 (m.d 3 4) (by simp) with h6227 | h6227
                                        · rcases p6220_3 (m.d 4 5) (by simp) with h6228 | h6228
                                          · linarith only [h5897, h6228, hlam]
                                          · linarith only [h6139, h6228, hlam]
                                        · linarith only [h6098, h6227, hlam]
                                    · linarith only [h5899, h6224, hlam]
                                  · linarith only [h5035, h6223, hlam]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5037, hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h3667, h5901, h6098, h6139, hc23, hc34, hlam, hphi, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5897, h5901, h6098, h6139, hc23, hc34, hlam, hphi, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  rcases p6220_3 (m.d 0 4) (by simp) with h6238 | h6238
                                  · linarith only [h3667, h6238, hlam]
                                  · linarith only [h5035, h6238, hlam]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5901, hlam, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5901, h6098, h6139, hc23, hc34, hlam, hphi, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5035, hlam, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5899, hlam, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h6098, hlam, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h6139, hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5897, h6098, h6139, hc23, hc34, hlam, hphi, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h3667, hc01, hc34, hlam, hphi, ht12, ht23, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  rcases p6220_3 (m.d 0 4) (by simp) with h6250 | h6250
                                  · linarith only [h5037, h6250, hlam]
                                  · linarith only [h5035, h6250, hlam]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h6098, h6139, hc23, hc34, hlam, hphi, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5897, hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h6097, hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h5037, h5897, h6098, hc23, hc34, hlam, hphi, p6220_1]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [h6188, hlam, p6220_0]
                                · have p6220_0 := h6220c.1
                                  have p6220_1 := h6220c.2.1
                                  have p6220_2 := h6220c.2.2.1
                                  have p6220_3 := h6220c.2.2.2
                                  linarith only [hlam, p6220_0]
                        · linarith only [h5900, h6213, hlam]
                      · linarith only [h6212, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6189_1]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      rcases p6189_3 (m.d 0 2) (by simp) with h6264 | h6264
                      · linarith only [h0, h6264, hlam]
                      · linarith only [h5034, h6264, hlam]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      rcases p6189_3 (m.d 0 2) (by simp) with h6267 | h6267
                      · linarith only [h0, h6267, hlam]
                      · linarith only [h5035, h6267, hlam]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      rcases p6189_3 (m.d 0 2) (by simp) with h6270 | h6270
                      · linarith only [h0, h6270, hlam]
                      · linarith only [h5036, h6270, hlam]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5034, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5898, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h6098, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h6100, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5035, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5899, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6189_1]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h6139, hlam, p6189_1]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5036, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h5900, hlam, p6189_0]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6189_1]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [h0, h5036, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6189_1]
                    · have p6189_0 := h6189c.1
                      have p6189_1 := h6189c.2.1
                      have p6189_2 := h6189c.2.2.1
                      have p6189_3 := h6189c.2.2.2
                      linarith only [hlam, p6189_0]
                  · linarith only [h3667, h5897, h5901, h6188, hlam]
          · linarith only [h3667, h5897, h6097, hlam]
      · linarith only [h0, h5036, h5900, hlam]
    · linarith only [h0, h5035, h5899, hlam]
  · linarith only [h0, h5034, h5898, hlam]

end R2N4
