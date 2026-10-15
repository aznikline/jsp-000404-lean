import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1904 | h1904
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1905 | h1905
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1906 | h1906
      · linarith only [h0, h1, h1906, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1908 | h1908
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1909 | h1909
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1910 | h1910
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1911 | h1911
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1912 | h1912
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1913 | h1913
                  · linarith only [h1906, h1908, h1912, h1913, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1915 | h1915
                    · rcases h0bigk with h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c | h1916c
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1908, h1912, hc01, hlam, hphi, ht0b, ht5b, p1916_1, u5ehi4]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, h1912, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1916_1, u5ehi4]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1916_1, u5ehi0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h0, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1906, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1912, hc02, hlam, hphi, ht0b, ht5b, p1916_1, u5ehi4]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h0, h1, h1905, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1916_1, u5ehi1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, h1913, hc01, hc23, hlam, hphi, ht12, p1916_1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, h1913, hc02, hc23, hlam, hphi, p1916_1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, h1912, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1916_1, u5ehi4]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1, h1905, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1916_1, u5ehi1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1904, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1908, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1910, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h0, h1905, h1908, hc01, hlam, hphi, ht0b, ht5b, p1916_1, u5ehi1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1905, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1909, hlam, p1916_1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1911, hlam, p1916_0]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [h1912, hlam, p1916_1]
                      · have p1916_0 := h1916c.1
                        have p1916_1 := h1916c.2.1
                        have p1916_2 := h1916c.2.2.1
                        have p1916_3 := h1916c.2.2.2
                        linarith only [hlam, p1916_0]
                    · linarith only [h0, h1, h1913, h1915, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1943 | h1943
                  · linarith only [h0, h1, h1906, h1943, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1945 | h1945
                    · rcases h0bigk with h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c | h1946c
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1909, hc01, hlam, hphi, ht0b, ht5b, p1946_1, u5ehi2]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, h1943, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1946_1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, h1943, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1946_1, u5ehi0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h0, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1906, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h0, h1, h1904, h1943, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1946_1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h0, h1, h1905, h1943, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1946_1, u5ehi1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, h1943, hc01, hc23, hlam, hphi, ht12, p1946_1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, h1943, hc02, hc23, hlam, hphi, p1946_1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        rcases p1946_3 (m.d 0 1) (by simp) with h1960 | h1960
                        · linarith only [h1, h1960, hlam]
                        · linarith only [h1904, h1960, hlam]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, h1905, h1943, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1946_1, u5ehi1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1904, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1908, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1910, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1912, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1905, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1909, hlam, p1946_1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1911, hlam, p1946_0]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [h1, h1905, h1908, h1943, h1945, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1946_1]
                      · have p1946_0 := h1946c.1
                        have p1946_1 := h1946c.2.1
                        have p1946_2 := h1946c.2.2.1
                        have p1946_3 := h1946c.2.2.2
                        linarith only [hlam, p1946_0]
                    · linarith only [h0, h1, h1943, h1945, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h1, h1909, h1911, hlam]
            · linarith only [h1, h1904, h1910, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1977 | h1977
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1978 | h1978
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1979 | h1979
                · linarith only [h1908, h1909, h1979, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1981 | h1981
                  · linarith only [h0, h1, h1906, h1981, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1983 | h1983
                    · rcases h0bigk with h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c | h1984c
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, h1908, h1981, h1983, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, h1981, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, h1981, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1984_1, u5ehi0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h0, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1906, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h0, h1, h1904, h1981, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1909, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, h1981, hc02, hc23, hlam, hphi, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        rcases p1984_3 (m.d 0 1) (by simp) with h1998 | h1998
                        · linarith only [h1, h1998, hlam]
                        · linarith only [h1904, h1998, hlam]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, h1908, h1909, h1981, h1983, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1904, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1908, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1977, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1979, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1905, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1908, h1983, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1978, hlam, p1984_0]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [h1, h1905, h1908, h1981, h1983, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1984_1]
                      · have p1984_0 := h1984c.1
                        have p1984_1 := h1984c.2.1
                        have p1984_2 := h1984c.2.2.1
                        have p1984_3 := h1984c.2.2.2
                        linarith only [hlam, p1984_0]
                    · linarith only [h0, h1, h1981, h1983, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1905, h1978, hlam]
            · linarith only [h1, h1905, h1908, h1909, h1977, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2015 | h2015
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2016 | h2016
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2017 | h2017
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2018 | h2018
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2019 | h2019
                  · linarith only [h0, h1906, h2015, h2019, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2021 | h2021
                    · rcases h0bigk with h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c | h2022c
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h2015, h2019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2022_1, u5ehi2]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h1908, h2015, h2019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2022_1, u5ehi2]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h2019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2022_1, u5ehi0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h0, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1906, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1908, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1905, hc02, hlam, hphi, ht0b, ht5b, p2022_1, u5ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h2019, hc01, hc23, hlam, hphi, ht12, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h2019, hc02, hc23, hlam, hphi, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h1908, h2015, h2019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2022_1, u5ehi2]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h1905, h2019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2022_1, u5ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1904, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1904, h2015, hc01, hlam, hphi, ht0b, ht5b, p2022_1, u5ehi2]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2016, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1, h1904, h1905, h2019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2022_1, u5ehi1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h1905, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2015, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2017, hlam, p2022_0]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [h2018, hlam, p2022_1]
                      · have p2022_0 := h2022c.1
                        have p2022_1 := h2022c.2.1
                        have p2022_2 := h2022c.2.2.1
                        have p2022_3 := h2022c.2.2.2
                        linarith only [hlam, p2022_0]
                    · linarith only [h1, h1904, h2016, h2019, h2021, hlam]
                · linarith only [h1908, h2015, h2018, hlam]
              · linarith only [h1, h1904, h1908, h2015, h2017, hlam]
            · linarith only [h1, h1904, h2016, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2052 | h2052
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2053 | h2053
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2054 | h2054
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2055 | h2055
                  · linarith only [h0, h1906, h2055, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2057 | h2057
                    · rcases h0bigk with h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c | h2058c
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h0, h1, h2055, hc12, hc23, hlam, hphi, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1, h2055, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2058_1, u5ehi0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h0, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1906, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1908, hlam, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h2015, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h0, h1, h2055, hc12, hc23, hlam, hphi, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1, h2054, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2058_1, u5ehi4]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1, h1905, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2058_1, u5ehi1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1904, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h0, h1, h1904, h2055, hc12, hc23, hlam, hphi, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h2052, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1, h1904, h1905, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2058_1, u5ehi1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h1905, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h0, h1, h1905, h2055, hc12, hc23, hlam, hphi, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h2053, hlam, p2058_0]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [h2054, hlam, p2058_1]
                      · have p2058_0 := h2058c.1
                        have p2058_1 := h2058c.2.1
                        have p2058_2 := h2058c.2.2.1
                        have p2058_3 := h2058c.2.2.2
                        linarith only [hlam, p2058_0]
                    · linarith only [h1, h1904, h2052, h2055, h2057, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2085 | h2085
                  · linarith only [h0, h1906, h2085, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2087 | h2087
                    · rcases h0bigk with h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, h2085, hc02, hc23, hlam, hphi, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, h2085, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, h2085, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2088_1, u5ehi0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h0, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1906, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1908, hlam, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h2015, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, h2085, hc01, hc23, hlam, hphi, ht12, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h0, h1, h2085, hc12, hc23, hlam, hphi, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h0, h1, h1908, h2085, hc12, hc23, hlam, hphi, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, h2053, h2085, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2088_1, u5ehi3]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1904, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h0, h1, h1904, h2085, hc12, hc23, hlam, hphi, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h2052, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h2054, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1905, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h0, h1, h1905, h2085, hc12, hc23, hlam, hphi, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h2053, hlam, p2088_0]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [h1, h1905, h2085, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2088_1]
                      · have p2088_0 := h2088c.1
                        have p2088_1 := h2088c.2.1
                        have p2088_2 := h2088c.2.2.1
                        have p2088_3 := h2088c.2.2.2
                        linarith only [hlam, p2088_0]
                    · linarith only [h0, h1, h2085, h2087, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1905, h2053, hlam]
            · linarith only [h1, h1904, h2052, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2117 | h2117
      · linarith only [h0, h1, h2117, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2119 | h2119
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2120 | h2120
          · linarith only [h0, h1905, h2120, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2122 | h2122
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2123 | h2123
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2124 | h2124
                · linarith only [h0, h1905, h2119, h2124, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2126 | h2126
                  · linarith only [h0, h1, h2117, h2119, h2126, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2128 | h2128
                    · rcases h0bigk with h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h1, h2119, h2126, h2128, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h1, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h1, h2126, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h1905, hlam, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h0, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2117, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h0, h1, h1904, h2126, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2120, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h1, h2126, hc02, hc23, hlam, hphi, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        rcases p2129_3 (m.d 0 1) (by simp) with h2143 | h2143
                        · linarith only [h1, h2143, hlam]
                        · linarith only [h1904, h2143, hlam]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h0, h1, h1905, h2126, hc12, hc23, hlam, hphi, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h1904, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2119, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2122, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2124, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2119, h2124, h2128, hc34, hc45, hlam, hphi, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2123, hlam, p2129_0]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [h2119, h2124, h2128, hc34, hc45, hlam, hphi, p2129_1]
                      · have p2129_0 := h2129c.1
                        have p2129_1 := h2129c.2.1
                        have p2129_2 := h2129c.2.2.1
                        have p2129_3 := h2129c.2.2.2
                        linarith only [hlam, p2129_0]
                    · linarith only [h0, h1, h2126, h2128, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2158 | h2158
                · linarith only [h0, h1905, h2119, h2158, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2160 | h2160
                  · linarith only [h0, h1, h2117, h2160, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2162 | h2162
                    · rcases h0bigk with h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c | h2163c
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2119, h2162, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h1, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h1, h2123, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h1905, hlam, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h0, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2117, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h1904, h2120, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2120, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2123, hc01, hc35, hlam, hphi, ht12, ht23, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2123, hc02, hc35, hlam, hphi, ht23, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2119, h2123, h2162, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2123, hlam, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h1904, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2119, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2122, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2158, hlam, p2163_0]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2120, hc01, hc25, hlam, hphi, ht12, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2119, h2120, h2162, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2123, hc03, hc35, hlam, hphi, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [h2119, h2158, h2162, hc34, hc45, hlam, hphi, p2163_1]
                      · have p2163_0 := h2163c.1
                        have p2163_1 := h2163c.2.1
                        have p2163_2 := h2163c.2.2.1
                        have p2163_3 := h2163c.2.2.2
                        linarith only [hlam, p2163_0]
                    · linarith only [h0, h1, h2160, h2162, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1904, h2122, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2191 | h2191
          · linarith only [h1904, h1905, h2119, h2191, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2193 | h2193
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2194 | h2194
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2195 | h2195
                · linarith only [h1904, h1905, h2195, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2197 | h2197
                  · linarith only [h0, h1, h2117, h2197, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2199 | h2199
                    · rcases h0bigk with h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c | h2200c
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, h1, h2197, hc12, hc23, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h1, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h1, h2197, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h1905, hlam, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2117, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2119, hlam, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2191, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, h1, h2197, hc12, hc23, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, h1, h2119, h2197, hc12, hc23, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, h1, h1905, h2197, hc12, hc23, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h1904, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, h1904, h1905, h2191, hc12, hc25, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2193, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2195, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2191, hc01, hc25, hlam, hphi, ht12, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h0, h2191, hc12, hc25, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2194, hlam, p2200_0]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [h2195, hc04, hc45, hlam, hphi, p2200_1]
                      · have p2200_0 := h2200c.1
                        have p2200_1 := h2200c.2.1
                        have p2200_2 := h2200c.2.2.1
                        have p2200_3 := h2200c.2.2.2
                        linarith only [hlam, p2200_0]
                    · linarith only [h0, h1, h2197, h2199, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2227 | h2227
                · linarith only [h1904, h1905, h2227, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2229 | h2229
                  · linarith only [h0, h2117, h2229, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2231 | h2231
                    · rcases h0bigk with h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c | h2232c
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h1, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h1905, hlam, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2117, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2119, hlam, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2191, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h2194, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h1, h2229, hc12, hc23, hlam, hphi, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h1, h2119, h2229, hc12, hc23, hlam, hphi, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2194, hlam, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h1904, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h1, h1904, h2229, hc12, hc23, hlam, hphi, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2193, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2227, hlam, p2232_0]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2191, hc01, hc25, hlam, hphi, ht12, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h0, h2191, hc12, hc25, hlam, hphi, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2194, hc03, hc35, hlam, hphi, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [h2227, hc04, hc45, hlam, hphi, p2232_1]
                      · have p2232_0 := h2232c.1
                        have p2232_1 := h2232c.2.1
                        have p2232_2 := h2232c.2.2.1
                        have p2232_3 := h2232c.2.2.2
                        linarith only [hlam, p2232_0]
                    · linarith only [h0, h1, h2193, h2229, h2231, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1, h1904, h2193, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2260 | h2260
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2261 | h2261
      · linarith only [h0, h1, h2261, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2263 | h2263
        · linarith only [h0, h1904, h2263, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2265 | h2265
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2266 | h2266
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2267 | h2267
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2268 | h2268
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2269 | h2269
                  · linarith only [h2261, h2265, h2269, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2271 | h2271
                    · rcases h0bigk with h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c | h2272c
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2265, hc01, hlam, hphi, ht0b, ht5b, p2272_1, u5ehi2]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1904, hlam, p2272_1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, h2269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2272_1, u5ehi0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h0, hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2261, hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2263, hlam, p2272_1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2260, hc02, hlam, hphi, ht0b, ht5b, p2272_1, u5ehi1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, h2269, hc01, hc23, hlam, hphi, ht12, p2272_1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, h2269, hc02, hc23, hlam, hphi, p2272_1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, h2268, h2269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2272_1, u5ehi4]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, h2260, h2269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2272_1, u5ehi1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h0, h2265, hc04, hlam, hphi, ht0b, ht5b, p2272_1, u5ehi2]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2263, h2265, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2272_1, u5ehi2]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2266, hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h1, h2260, h2266, h2269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2272_1, u5ehi1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2260, hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2265, hlam, p2272_1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2267, hlam, p2272_0]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [h2268, hlam, p2272_1]
                      · have p2272_0 := h2272c.1
                        have p2272_1 := h2272c.2.1
                        have p2272_2 := h2272c.2.2.1
                        have p2272_3 := h2272c.2.2.2
                        linarith only [hlam, p2272_0]
                    · linarith only [h1, h2266, h2269, h2271, hlam]
                · linarith only [h1904, h2260, h2268, hlam]
              · linarith only [h0, h1904, h2265, h2266, h2267, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2301 | h2301
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2302 | h2302
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2303 | h2303
                  · linarith only [h0, h1, h2266, h2303, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2305 | h2305
                    · linarith only [h0, h1, h2266, h2305, hc12, hc23, hlam, hphi]
                    · linarith only [h2261, h2265, h2305, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h0, h1, h2265, h2266, h2302, hlam]
              · linarith only [h0, h1, h2265, h2301, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2310 | h2310
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2311 | h2311
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2312 | h2312
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2313 | h2313
                  · linarith only [h0, h1, h2261, h2313, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2315 | h2315
                    · rcases h0bigk with h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h1, h2313, hc12, hc23, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1904, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1, h2313, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2316_1, u5ehi0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2261, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2263, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2265, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h1, h2313, hc12, hc23, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1, h1904, h2313, hc01, hc23, hlam, hphi, ht12, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1, h2260, h2313, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2316_1, u5ehi1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2260, hc04, hlam, hphi, ht0b, ht5b, p2316_1, u5ehi1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h2263, h2315, hc12, hc23, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2310, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h1, h2260, h2310, h2313, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2316_1, u5ehi1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2260, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h0, h1, h2260, h2313, hc12, hc23, hlam, hphi, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2311, hlam, p2316_0]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [h2312, hlam, p2316_1]
                      · have p2316_0 := h2316c.1
                        have p2316_1 := h2316c.2.1
                        have p2316_2 := h2316c.2.2.1
                        have p2316_3 := h2316c.2.2.2
                        linarith only [hlam, p2316_0]
                    · linarith only [h1, h2310, h2313, h2315, hlam]
                · linarith only [h1904, h2260, h2312, hlam]
              · linarith only [h1, h2260, h2311, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2345 | h2345
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2346 | h2346
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2347 | h2347
                  · linarith only [h0, h1, h2310, h2347, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2349 | h2349
                    · linarith only [h0, h1, h2310, h2349, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h2260, h2347, h2349, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h1, h2260, h2310, h2346, hlam]
              · linarith only [h1, h2260, h2345, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2354 | h2354
      · linarith only [h0, h1, h2354, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2356 | h2356
        · linarith only [h0, h1904, h2356, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2358 | h2358
          · linarith only [h0, h2260, h2358, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2360 | h2360
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2361 | h2361
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2362 | h2362
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2363 | h2363
                  · linarith only [h0, h1, h2354, h2363, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2365 | h2365
                    · rcases h0bigk with h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c | h2366c
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h1, h2363, hc12, hc23, hlam, hphi, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h1, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h1904, hlam, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2260, hlam, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2354, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2356, hlam, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2358, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h1, h2363, hc12, hc23, hlam, hphi, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h1, h2362, h2363, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2366_1, u5ehi4]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h1, h2260, h2363, hc12, hc23, hlam, hphi, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h2356, hc12, hc24, hlam, hphi, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2360, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h1, h2260, h2360, h2363, hc12, hc23, hlam, hphi, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h0, h2358, hc12, hc25, hlam, hphi, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2361, hlam, p2366_0]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [h2362, hlam, p2366_1]
                      · have p2366_0 := h2366c.1
                        have p2366_1 := h2366c.2.1
                        have p2366_2 := h2366c.2.2.1
                        have p2366_3 := h2366c.2.2.2
                        linarith only [hlam, p2366_0]
                    · linarith only [h1, h2360, h2363, h2365, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2393 | h2393
                  · linarith only [h0, h1904, h2362, h2393, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2395 | h2395
                    · rcases h0bigk with h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h1904, h2362, hc02, hc45, hlam, hphi, ht23, ht34, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h1, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h1904, hlam, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2260, hlam, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2354, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2356, hlam, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2358, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h1, h2393, hc12, hc23, hlam, hphi, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h1, h1904, h2393, hc12, hc23, hlam, hphi, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h1, h1904, h2362, h2393, hc12, hc23, hlam, hphi, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h2362, hc12, hc45, hlam, hphi, ht23, ht34, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2360, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2362, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h2260, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h2358, hc12, hc25, hlam, hphi, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h2361, hlam, p2396_0]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [h0, h1, h1904, h2361, h2393, hc12, hc23, hlam, hphi, p2396_1]
                      · have p2396_0 := h2396c.1
                        have p2396_1 := h2396c.2.1
                        have p2396_2 := h2396c.2.2.1
                        have p2396_3 := h2396c.2.2.2
                        linarith only [hlam, p2396_0]
                    · linarith only [h0, h1, h2393, h2395, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2423 | h2423
                · linarith only [h2360, h2361, h2423, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2425 | h2425
                  · linarith only [h0, h1, h2354, h2360, h2425, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2427 | h2427
                    · rcases h0bigk with h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c | h2428c
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h1, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h1, hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h1904, hlam, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2260, hlam, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h0, hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2354, hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2356, hlam, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2358, hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2361, hc01, hc35, hlam, hphi, ht12, ht23, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h0, h2361, hc12, hc35, hlam, hphi, ht23, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2361, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2361, hlam, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h0, h2423, hc12, hc45, hlam, hphi, ht23, ht34, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2360, hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2423, hlam, p2428_0]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h0, h2358, hc12, hc25, hlam, hphi, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2361, hc03, hc35, hlam, hphi, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [h2423, hc04, hc45, hlam, hphi, p2428_1]
                      · have p2428_0 := h2428c.1
                        have p2428_1 := h2428c.2.1
                        have p2428_2 := h2428c.2.2.1
                        have p2428_3 := h2428c.2.2.2
                        linarith only [hlam, p2428_0]
                    · linarith only [h0, h1, h2425, h2427, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2455 | h2455
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2456 | h2456
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2457 | h2457
                  · linarith only [h0, h2354, h2457, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2459 | h2459
                    · linarith only [h2360, h2455, h2459, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h1, h2457, h2459, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2360, h2455, h2456, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2463 | h2463
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2464 | h2464
                  · linarith only [h0, h1, h2455, h2464, hc23, hc35, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2466 | h2466
                    · linarith only [h0, h1, h2360, h2466, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h2464, h2466, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2469 | h2469
                  · linarith only [h0, h1, h2354, h2469, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2471 | h2471
                    · linarith only [h0, h1, h2360, h2471, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h2469, h2471, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
