import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S0
import Jsp000404.R1LeavesN7_53S2
import Jsp000404.R1LeavesN7_53S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1561 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1906 | h1906
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1907 | h1907
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1908 | h1908
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1909 | h1909
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1910 | h1910
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1911 | h1911
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1912 | h1912
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1914 | h1914
                  · linarith only [h1559, h1561, h1906, h1912, h1914, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1916 | h1916
                    · linarith only [h1557, h1914, h1916, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases h0emax with h1918 | h1918 | h1918 | h1918 | h1918
                      · rcases h5bigk with h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h674, hlam, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1557, hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1557, h1914, hc45, hlam, hphi, ht34, p1919_1, u3ehi4]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1561, hlam, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1908, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1919_1, u2ehi4]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1906, h1910, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1919_1, u3ehi4]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1906, h1909, h1911, h1914, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1919_1, u2ehi0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1908, hlam, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1906, h1913, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1919_1, u3ehi4]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1914, hlam, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1560, hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1910, hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1913, hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1916, hlam, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p1919_1, u2ehi0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1911, hlam, p1919_0]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1906, h1909, h1911, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1919_1]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [h1906, h1909, h1911, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1919_1, u3ehi4]
                        · have p1919_0 := h1919c.1
                          have p1919_1 := h1919c.2.1
                          have p1919_2 := h1919c.2.2.1
                          have p1919_3 := h1919c.2.2.2
                          linarith only [hlam, p1919_0]
                      · rcases h5bigk with h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h674, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1557, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1916, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1945_1, u3ehi3]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1561, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1906, h1909, h1911, h674, hc01, hc12, hlam, hphi, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1557, h1906, h1909, h1911, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1945_1, u2ehi0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1906, h1909, h1911, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1945_1, u3ehi3]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1561, h1906, h1909, h1911, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1945_1, u2ehi0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1908, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1906, h1913, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1945_1, u3ehi3]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1914, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1560, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1910, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1913, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1916, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p1945_1, u2ehi0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1911, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1906, h1909, h1911, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1906, h1909, h1911, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1945_1, u3ehi3]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                      · linarith only [h1559, h1918, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases h5bigk with h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c | h1972c
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h674, hlam, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1557, hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1916, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1972_1, u3ehi3]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1561, hlam, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1906, h1909, h1911, h674, hc01, hc12, hlam, hphi, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1557, h1906, h1909, h1911, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1972_1, u2ehi0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1906, h1909, h1911, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1972_1, u3ehi3]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1559, h1561, h1906, h1909, h1911, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1972_1, u3ehi3]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1972_1, u2ehi0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1908, hlam, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1906, h1913, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1972_1, u3ehi3]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1914, hlam, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1560, hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1910, hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1913, hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1916, hlam, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p1972_1, u2ehi0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1911, hlam, p1972_0]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1906, h1909, h1911, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1972_1]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [h1906, h1909, h1911, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1972_1, u3ehi3]
                        · have p1972_0 := h1972c.1
                          have p1972_1 := h1972c.2.1
                          have p1972_2 := h1972c.2.2.1
                          have p1972_3 := h1972c.2.2.2
                          linarith only [hlam, p1972_0]
                      · rcases h5bigk with h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h674, hlam, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1557, hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1916, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1998_1, u3ehi3]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1561, hlam, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1906, h1909, h1911, h674, hc01, hc12, hlam, hphi, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1557, h1906, h1909, h1911, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1998_1, u2ehi0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1906, h1909, h1911, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1998_1, u3ehi3]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1559, h1561, h1906, h1909, h1911, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1998_1, u3ehi3]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p1998_1, u2ehi0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1908, hlam, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1906, h1913, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1998_1, u3ehi3]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1914, hlam, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1560, hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1910, hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1913, hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1916, hlam, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p1998_1, u2ehi0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1911, hlam, p1998_0]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1906, h1909, h1911, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1998_1]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [h1906, h1909, h1911, h1916, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1998_1, u3ehi3]
                        · have p1998_0 := h1998c.1
                          have p1998_1 := h1998c.2.1
                          have p1998_2 := h1998c.2.2.1
                          have p1998_3 := h1998c.2.2.2
                          linarith only [hlam, p1998_0]
                · linarith only [h1560, h1913, h855, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h1912, h855, hc34, hlam, hphi, ht23, u2ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2026 | h2026
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2027 | h2027
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2028 | h2028
                  · linarith only [h1559, h1561, h1907, h2028, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2030 | h2030
                    · linarith only [h1557, h1908, h1911, h2030, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases h0emax with h2032 | h2032 | h2032 | h2032 | h2032
                      · rcases h5bigk with h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c | h2033c
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h674, hlam, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1557, hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h2030, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2033_1, u3ehi3]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1561, hlam, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1911, h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1557, h1911, hc45, hlam, hphi, ht23, ht34, p2033_1, u2ehi0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1911, h2030, hc45, hlam, hphi, ht34, p2033_1, u3ehi3]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1911, hlam, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1557, h1906, h2027, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2033_1, u2ehi0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1908, hlam, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1906, h2027, h2030, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2033_1, u3ehi3]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h2028, hlam, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1560, hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1910, hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h2027, hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [hlam, p2033_0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h2030, hlam, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2033_1, u2ehi0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2033_1]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2033_1, u2ehi0]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [h2030, hc45, hlam, hphi, ht34, p2033_1, u3ehi3]
                        · have p2033_0 := h2033c.1
                          have p2033_1 := h2033c.2.1
                          have p2033_2 := h2033c.2.2.1
                          have p2033_3 := h2033c.2.2.2
                          linarith only [hlam, p2033_0]
                      · rcases h5bigk with h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h674, hlam, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1557, hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h2030, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2059_1, u3ehi3]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1561, hlam, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1557, h1908, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2059_1, u2ehi0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1906, h1910, h2030, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2059_1, u3ehi3]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1911, hlam, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1557, h2027, hc23, hlam, hphi, p2059_1, u2ehi0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1908, hlam, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1906, h2027, h2030, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2059_1, u3ehi3]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h2028, hlam, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1560, hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1910, hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h2027, hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [hlam, p2059_0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h2030, hlam, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2059_1, u2ehi0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2059_1]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2059_1, u2ehi0]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [h2030, hc45, hlam, hphi, ht34, p2059_1, u3ehi3]
                        · have p2059_0 := h2059c.1
                          have p2059_1 := h2059c.2.1
                          have p2059_2 := h2059c.2.2.1
                          have p2059_3 := h2059c.2.2.2
                          linarith only [hlam, p2059_0]
                      · linarith only [h1559, h2032, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases h5bigk with h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h674, hlam, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1557, hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h2030, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2086_1, u3ehi3]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1561, hlam, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1557, h1908, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2086_1, u2ehi0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1906, h1910, h2030, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2086_1, u3ehi3]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1911, hlam, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1557, h2027, hc23, hlam, hphi, p2086_1, u2ehi0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1908, hlam, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1906, h2027, h2030, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2086_1, u3ehi3]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h2028, hlam, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1560, hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1910, hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h2027, hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [hlam, p2086_0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h2030, hlam, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2086_1, u2ehi0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2086_1]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2086_1, u2ehi0]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [h2030, hc45, hlam, hphi, ht34, p2086_1, u3ehi3]
                        · have p2086_0 := h2086c.1
                          have p2086_1 := h2086c.2.1
                          have p2086_2 := h2086c.2.2.1
                          have p2086_3 := h2086c.2.2.2
                          linarith only [hlam, p2086_0]
                      · rcases h5bigk with h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h674, hlam, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1557, hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h2030, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2112_1, u3ehi3]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1561, hlam, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1557, h1908, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2112_1, u2ehi0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1906, h1910, h2030, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2112_1, u3ehi3]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1911, hlam, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p2112_1, u2ehi0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1908, hlam, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h2027, h2030, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2112_1, u3ehi3]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h2028, hlam, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1560, hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1910, hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h2027, hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [hlam, p2112_0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h2030, hlam, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2112_1, u2ehi0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2112_1]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2112_1, u2ehi0]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [h2030, hc45, hlam, hphi, ht34, p2112_1, u3ehi3]
                        · have p2112_0 := h2112c.1
                          have p2112_1 := h2112c.2.1
                          have p2112_2 := h2112c.2.2.1
                          have p2112_3 := h2112c.2.2.2
                          linarith only [hlam, p2112_0]
                · linarith only [h1560, h2027, h855, hlam]
              · linarith only [h1560, h2026, h855, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1560, h1906, h1910, h855, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h1906, h1909, h855, hc34, hlam, hphi, ht23, u2ehi0]
      · linarith only [h1906, h1908, h855, hc25, hlam, hphi, u2ehi0]
    · linarith only [h1906, h1907, h855, hc24, hlam, hphi, u2ehi0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2144 | h2144
    · linarith only [h1906, h2144, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2146 | h2146
      · linarith only [h1906, h2146, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2148 | h2148
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2149 | h2149
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2151 | h2151
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2152 | h2152
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2153 | h2153
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2154 | h2154
                    · linarith only [h1559, h1561, h2154, hlam]
                    · rcases h0emax with h2156 | h2156 | h2156 | h2156 | h2156
                      · rcases h5bigk with h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c | h2157c
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h674, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1557, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1561, h1906, h2148, h2150, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1561, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2146, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2157_1, u3ehi4]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1561, h1906, h2148, h2150, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1557, hc25, hlam, hphi, p2157_1, u2ehi0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h674, hc01, hc25, hlam, hphi, ht12, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2152, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2157_1, u3ehi4]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1559, h1561, h2151, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2157_1, u3ehi3]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1560, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2149, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2152, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2154, hlam, p2157_1]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2157_1, u2ehi0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2150, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h2153, hlam, p2157_0]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [h1906, h2148, h2150, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2157_1, u3ehi4]
                        · have p2157_0 := h2157c.1
                          have p2157_1 := h2157c.2.1
                          have p2157_2 := h2157c.2.2.1
                          have p2157_3 := h2157c.2.2.2
                          linarith only [hlam, p2157_0]
                      · rcases h5bigk with h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c | h2183c
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h674, hlam, p2183_1]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1557, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2154, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2183_1, u3ehi3]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1561, hlam, p2183_1]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p2183_1]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2146, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2146, h2151, h2153, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2183_1, u3ehi3]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1561, h2146, h2151, h2153, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2183_1]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1557, h2151, h2153, hc23, hlam, hphi, p2183_1, u2ehi0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2151, h2153, h674, hc01, hc23, hlam, hphi, ht12, p2183_1]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2151, h2153, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2183_1, u3ehi3]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1559, h1561, h2151, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2183_1, u3ehi3]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1560, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2149, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2152, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2154, hlam, p2183_1]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1557, hc45, hlam, hphi, ht23, ht34, p2183_1, u2ehi0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2150, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h2153, hlam, p2183_0]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [h1906, h2148, h2150, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2183_1, u3ehi3]
                        · have p2183_0 := h2183c.1
                          have p2183_1 := h2183c.2.1
                          have p2183_2 := h2183c.2.2.1
                          have p2183_3 := h2183c.2.2.2
                          linarith only [hlam, p2183_0]
                      · linarith only [h1559, h2156, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases h5bigk with h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c | h2210c
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h674, hlam, p2210_1]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1557, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2154, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2210_1, u3ehi3]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1561, hlam, p2210_1]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h674, hc01, hc15, hlam, hphi, p2210_1]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2146, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2146, h2151, h2153, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2210_1, u3ehi3]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1561, h2146, h2151, h2153, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2210_1]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1557, h2151, h2153, hc23, hlam, hphi, p2210_1, u2ehi0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2151, h2153, h674, hc01, hc23, hlam, hphi, ht12, p2210_1]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2151, h2153, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2210_1, u3ehi3]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1559, h1561, h2151, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2210_1, u3ehi3]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1560, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2149, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2152, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2154, hlam, p2210_1]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1557, h2150, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2210_1, u2ehi0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2150, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h2153, hlam, p2210_0]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [h1906, h2148, h2150, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2210_1, u3ehi3]
                        · have p2210_0 := h2210c.1
                          have p2210_1 := h2210c.2.1
                          have p2210_2 := h2210c.2.2.1
                          have p2210_3 := h2210c.2.2.2
                          linarith only [hlam, p2210_0]
                      · rcases h5bigk with h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c | h2236c
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h674, hlam, p2236_1]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1557, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2154, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p2236_1, u3ehi3]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1561, hlam, p2236_1]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2146, h2151, h2153, h674, hc01, hc23, hlam, hphi, ht12, p2236_1]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2146, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2146, h2151, h2153, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2236_1, u3ehi3]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1559, h1561, h2146, h2151, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2236_1, u3ehi3]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1557, h2151, h2153, hc23, hlam, hphi, p2236_1, u2ehi0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2151, h2153, h674, hc01, hc23, hlam, hphi, ht12, p2236_1]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2151, h2153, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2236_1, u3ehi3]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1559, h1561, h2151, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2236_1, u3ehi3]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1560, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2149, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2152, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2154, hlam, p2236_1]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1557, h2150, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2236_1, u2ehi0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2150, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h2153, hlam, p2236_0]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [h1906, h2148, h2150, h2154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2236_1, u3ehi3]
                        · have p2236_0 := h2236c.1
                          have p2236_1 := h2236c.2.1
                          have p2236_2 := h2236c.2.2.1
                          have p2236_3 := h2236c.2.2.2
                          linarith only [hlam, p2236_0]
                  · linarith only [h1906, h2148, h2150, h2153, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1560, h1906, h2152, h482, hlam]
              · linarith only [h1559, h1561, h1906, h2148, h2150, h2151, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2265 | h2265
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2266 | h2266
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2267 | h2267
                  · linarith only [h0, h2144, h2150, h2267, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h2144, h2267, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h1560, h1906, h2266, h482, hlam]
              · linarith only [h1559, h1561, h1906, h2265, h482, hc45, hlam, hphi, ht34, u3ehi0]
          · linarith only [h1560, h2149, h482, hlam]
        · linarith only [h1559, h2148, h482, hlam]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1561 | h1561
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557 h1559 h1560 h1561
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557 h1559 h1560 h1561

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1560 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [h1559, h1560, hc35, hlam, hphi, u3ehi3]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1560 | h1560
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557 h1559 h1560
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557 h1559 h1560

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1559 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2275 | h2275
  · linarith only [h1559, h2275, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2277 | h2277
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2278 | h2278
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2279 | h2279
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2280 | h2280
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2281 | h2281
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2282 | h2282
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2283 | h2283
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2284 | h2284
                  · linarith only [h1559, h2284, h855, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h2278, h2281, h2284, h855, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h1559, h2277, h2278, h2279, h2281, h2283, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h1559, h2281, h2282, hc35, hlam, hphi, u3ehi0]
            · linarith only [h2278, h2281, h855, hc34, hlam, hphi, ht23, u2ehi0]
          · linarith only [h2278, h2280, h855, hc25, hlam, hphi, u2ehi0]
        · linarith only [h2278, h2279, h855, hc24, hlam, hphi, u2ehi0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2292 | h2292
        · linarith only [h2278, h2292, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2294 | h2294
          · linarith only [h2278, h2294, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2296 | h2296
            · linarith only [h1559, h2278, h2296, h855, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2298 | h2298
              · linarith only [h2296, h2298, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2300 | h2300
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2301 | h2301
                  · linarith only [h2278, h2296, h2301, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h2301, h855, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h0, h1559, h2277, h2292, h2300, hc01, hc34, hlam, hphi, ht12, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2305 | h2305
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2306 | h2306
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2307 | h2307
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2308 | h2308
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2309 | h2309
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2310 | h2310
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2311 | h2311
                  · linarith only [h1559, h2305, h2311, h855, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h2311, h855, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1559, h2308, h2310, h855, hc45, hlam, hphi, ht23, ht34, u2ehi0]
              · linarith only [h1559, h2308, h2309, h855, hc35, hlam, hphi, ht23, u2ehi0]
            · linarith only [h2305, h2308, h855, hc34, hlam, hphi, ht23, u2ehi0]
          · linarith only [h2305, h2307, h855, hc25, hlam, hphi, u2ehi0]
        · linarith only [h2305, h2306, h855, hc24, hlam, hphi, u2ehi0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2319 | h2319
        · linarith only [h2305, h2319, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2321 | h2321
          · linarith only [h2305, h2321, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2323 | h2323
            · linarith only [h1559, h2305, h2323, h855, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2325 | h2325
              · linarith only [h2323, h2325, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2327 | h2327
                · linarith only [h1559, h2277, h2319, h2327, h855, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2329 | h2329
                  · linarith only [h1559, h2329, h855, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h2329, h855, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1559 | h1559
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557 h1559
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557 h1559

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1557 | h1557
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h1557

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h855 | h855
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h674 | h674
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h482 h674
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h482 h674

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h482 | h482
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h482
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h482

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
